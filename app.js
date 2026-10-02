
const map=L.map('map').setView([55.58,-5.25],11);
L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',{maxZoom:19,attribution:'© OpenStreetMap contributors'}).addTo(map);

let graph,adj=new Map(),edgeMap=new Map(),layers=[],nodeLayers=new Map();
let routeSegments=[],current=null,startNode=null,routeLayer=null,choiceLayers=[],choiceFlowLayers=[],dragMarker=null;
let knownWalks=[],knownWalkMembership=new Map(),knownWalkMarkers=[],knownWalkIndexReady=false;

// OSM signposts: loaded from the POV association export and filtered client-side.
let osmSignposts=[];
let osmSignpostMarkers=[];
let osmNearbyLabelMarkers=[];
let osmWayfindingLines=[];
let osmWayfindingArrows=[];
let osmSignpostReady=false;
let signpostGroups=new Map();
let signpostTypes=new Map();
let lastSignpostBranches=[];
let selectedSignpostGroups=new Set();
let selectedSignpostTypes=new Set();
const DISPLAY_SIGNPOST_GROUPS=['HERITAGE','LANDSCAPE','ROUTE_FEATURE','VIEWS','SHELTER','WATER'];
const DEFAULT_SIGNPOST_GROUPS=['HERITAGE','LANDSCAPE','ROUTE_FEATURE','VIEWS','SHELTER'];
const SIGNPOST_MAX_DIRECTIONAL=1;
const SIGNPOST_MAX_NEARBY=12;
const SIGNPOST_DIRECTIONAL_LOOKAHEAD_M=2200;
const SIGNPOST_NEARBY_LOOKAHEAD_M=2600;
const SIGNPOST_NEAR_ROUTE_M=180;
const SIGNPOST_NEARBY_LABEL_M=900;


const starts=new Set();
const WALK_KMH=4.5;
const CHOICE_RADIUS_M=500;
const ORANGE='#f97316';
const BLUE='#2f80ed';
const GREY='#9aa0a6';

function hav(a,b){
  const R=6371008.8,p1=a[1]*Math.PI/180,p2=b[1]*Math.PI/180;
  const dp=(b[1]-a[1])*Math.PI/180,dl=(b[0]-a[0])*Math.PI/180;
  const x=Math.sin(dp/2)**2+Math.cos(p1)*Math.cos(p2)*Math.sin(dl/2)**2;
  return 2*R*Math.asin(Math.sqrt(x));
}
function addAdj(a,b,w,id){
  if(!adj.has(a))adj.set(a,[]);
  adj.get(a).push({to:b,w,id});
}
function nodeById(id){return graph.nodes.find(n=>n.id===id)}
function edgeBetween(a,b){
  const list=adj.get(a)||[];
  return list.find(e=>e.to===b);
}
function dijkstra(s,t){
  const d=new Map(),prev=new Map(),q=new Set(graph.nodes.map(n=>n.id));
  for(const n of q)d.set(n,Infinity);
  d.set(s,0);
  while(q.size){
    let u=null,du=Infinity;
    for(const x of q){if(d.get(x)<du){du=d.get(x);u=x}}
    if(u===null||du===Infinity)break;
    q.delete(u);
    if(u===t)break;
    for(const e of (adj.get(u)||[])){
      if(!q.has(e.to))continue;
      const nd=du+e.w;
      if(nd<d.get(e.to)){d.set(e.to,nd);prev.set(e.to,{u,e});}
    }
  }
  if(!prev.has(t)&&s!==t)return null;
  const ids=[],steps=[];let u=t;
  while(u!==s){
    const p=prev.get(u);if(!p)return null;
    ids.push(u);steps.push({from:p.u,to:u,edge:p.e});u=p.u;
  }
  ids.push(s);ids.reverse();steps.reverse();
  return {ids,steps,metres:d.get(t)};
}
function routeSteps(){
  return routeSegments.flatMap(s=>s.steps);
}
function routeCoordinates(){
  let coords=[];
  for(const step of routeSteps()){
    const e=edgeMap.get(step.edge.id);
    if(!e||!e.coords||!e.coords.length)continue;
    let c=(e.from===step.from&&e.to===step.to)?e.coords:[...e.coords].reverse();
    let latlngs=c.map(p=>[p[1],p[0]]);
    if(coords.length&&latlngs.length){
      const a=coords[coords.length-1],b=latlngs[0];
      if(Math.abs(a[0]-b[0])<1e-10&&Math.abs(a[1]-b[1])<1e-10)latlngs.shift();
    }
    coords.push(...latlngs);
  }
  return coords;
}
function drawRoute(){
  if(routeLayer)map.removeLayer(routeLayer);
  const coords=routeCoordinates();
  if(coords.length)routeLayer=L.polyline(coords,{color:ORANGE,weight:4,opacity:.98,lineCap:'round',lineJoin:'round',smoothFactor:0}).addTo(map);
}
function routeDistance(){return routeSegments.reduce((s,x)=>s+x.metres,0)}
function returnRoute(){
  if(current===null||startNode===null)return null;
  return dijkstra(current,startNode);
}
function fmtDist(m){return m<1000?`${Math.round(m)} m`:`${(m/1000).toFixed(1)} km`}
function fmtTime(min){
  const h=Math.floor(min/60),m=Math.round(min%60);
  return h?`${h}h ${m}m`:`${m}m`;
}
function routeTimeMinutes(m){return m/1000/WALK_KMH*60}
function elevationValue(n){
  if(!n)return null;
  const v=n.elevation??n.elev??n.z??n.altitude;
  return Number.isFinite(Number(v))?Number(v):null;
}
function elevationStats(){
  const ids=[];
  if(startNode!==null)ids.push(startNode);
  for(const s of routeSegments)ids.push(...s.steps.map(x=>x.to));
  const vals=ids.map(id=>elevationValue(nodeById(id))).filter(v=>v!==null);
  if(vals.length<2)return {up:null,down:null};
  let up=0,down=0,prev=vals[0];
  for(const v of vals.slice(1)){const d=v-prev;if(d>0)up+=d;else down+=-d;prev=v}
  return {up,down};
}
function updateStats(){
  const out=routeDistance();
  const back=returnRoute();
  const backM=back?back.metres:0;
  const estOut=routeTimeMinutes(out);
  const estBack=back?routeTimeMinutes(backM):0;
  const elev=elevationStats();
  document.getElementById('stats').innerHTML=
    `<b>${fmtDist(out)}</b> • ${fmtTime(estOut)}${back?` • return ${fmtDist(backM)} / ${fmtTime(estBack)}`:''}`;
  document.getElementById('detailStats').innerHTML=`
    <div><b>Walk so far</b><strong>${fmtDist(out)}</strong></div>
    <div><b>Walking time</b><strong>${fmtTime(estOut)}</strong></div>
    <div><b>Ascent</b><strong>${elev.up===null?'—':Math.round(elev.up)+' m'}</strong></div>
    <div><b>Descent</b><strong>${elev.down===null?'—':Math.round(elev.down)+' m'}</strong></div>
    <div><b>Return home</b><strong>${back?fmtDist(backM):'—'}</strong></div>
    <div><b>Total journey</b><strong>${back?fmtTime(estOut+estBack):'—'}</strong></div>`;
}
function clearKnownWalkMarkers(){
  for(const m of knownWalkMarkers)map.removeLayer(m);
  knownWalkMarkers=[];
}
function pointAlongCoords(coords, metres){
  if(!coords?.length) return null;
  if(coords.length===1) return coords[0];
  let used=0;
  for(let i=1;i<coords.length;i++){
    const a=coords[i-1],b=coords[i],seg=hav(a,b);
    if(used+seg>=metres){
      const t=seg>0?(metres-used)/seg:0;
      return [a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t];
    }
    used+=seg;
  }
  return coords[coords.length-1];
}
function knownWalkCandidatesForBranch(edgePath){
  if(!knownWalkIndexReady||!edgePath?.length)return [];
  const found=new Map();
  let cumulative=0;
  for(const eid of edgePath){
    const routeIds=knownWalkMembership.get(String(eid))||[];
    for(const rid of routeIds){
      if(!found.has(rid))found.set(rid,cumulative);
    }
    const edge=edgeMap.get(eid);
    cumulative += Number(edge?.w)||0;
  }
  return [...found.entries()]
    .map(([walkId,joinDistanceM])=>({
      walk:knownWalks.find(r=>r.walk_id===walkId),
      joinDistanceM
    }))
    .filter(x=>x.walk)
    .sort((a,b)=>a.joinDistanceM-b.joinDistanceM || a.walk.name.localeCompare(b.walk.name));
}
function renderKnownWalkList(items){
  const el=document.getElementById('knownWalkList');
  if(!el)return;
  if(!items.length){
    el.innerHTML='<span class="known-empty">No known walks encountered in the current choices.</span>';
    return;
  }
  el.innerHTML=items.map(x=>{
    const w=x.walk;
    const stats=[w.distance_km!=null?`${Number(w.distance_km).toFixed(1)} km`:null,
      w.ascent_m!=null?`+${Math.round(w.ascent_m)} m`:null,
      w.duration_min!=null?fmtTime(w.duration_min):null].filter(Boolean).join(' · ');
    return `<button class="known-walk-row" data-known-walk="${w.walk_id}"><strong>${escapeHtmlSafe(w.name)}</strong><span>${Math.round(x.joinDistanceM)} m ahead · ${escapeHtmlSafe(stats)}</span></button>`;
  }).join('');
  el.querySelectorAll('[data-known-walk]').forEach(btn=>btn.onclick=()=>{
    const w=knownWalks.find(r=>r.walk_id===btn.dataset.knownWalk);
    if(w) document.getElementById('info').textContent=`Known walk: ${w.name} · ${w.distance_km ?? '—'} km · ${w.ascent_m != null ? '+'+Math.round(w.ascent_m)+' m' : '—'} · ${w.duration_min != null ? fmtTime(w.duration_min) : 'time unavailable'}`;
  });
}
function escapeHtmlSafe(s){
  return String(s??'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
}
function renderKnownWalkSignposts(branches){
  clearKnownWalkMarkers();
  const all=[];
  for(const b of (branches||[])){
    for(const item of knownWalkCandidatesForBranch(b.edgePath)){
      const key=`${item.walk.walk_id}:${Math.round(item.joinDistanceM)}`;
      if(!all.some(x=>x.key===key)) all.push({...item,coords:b.coords,key});
    }
  }
  all.sort((a,b)=>a.joinDistanceM-b.joinDistanceM);
  const limited=all.slice(0,8);
  renderKnownWalkList(limited);
  for(const item of limited){
    const point=pointAlongCoords(item.coords,item.joinDistanceM);
    if(!point)continue;
    const w=item.walk;
    const stats=[w.distance_km!=null?`${Number(w.distance_km).toFixed(1)} km`:null,w.ascent_m!=null?`+${Math.round(w.ascent_m)} m`:null].filter(Boolean).join(' · ');
    const icon=L.divIcon({className:'known-walk-signpost',html:`<div>${escapeHtmlSafe(w.name)}<small>${Math.round(item.joinDistanceM)} m · ${escapeHtmlSafe(stats)}</small></div>`,iconSize:[1,1],iconAnchor:[0,0]});
    const marker=L.marker([point[1],point[0]],{icon,zIndexOffset:1200}).addTo(map);
    marker.on('click',()=>{
      document.getElementById('info').textContent=`Known walk: ${w.name} · ${w.distance_km ?? '—'} km · ${w.ascent_m != null ? '+'+Math.round(w.ascent_m)+' m' : '—'} · ${w.duration_min != null ? fmtTime(w.duration_min) : 'time unavailable'}`;
    });
    knownWalkMarkers.push(marker);
  }
}

function injectSignpostUI(){
  if(document.getElementById('signpostFilter'))return;
  const style=document.createElement('style');
  style.textContent=`
    #signpostFilter{position:fixed;left:14px;top:78px;width:238px;max-height:68vh;overflow:hidden;z-index:1800;background:rgba(250,249,246,.96);border:1px solid rgba(36,48,58,.10);border-radius:14px;box-shadow:0 10px 28px rgba(33,43,52,.14);font:13px/1.35 system-ui,-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;color:#24303a;backdrop-filter:blur(8px)}
    #signpostFilter .sf-head{display:flex;align-items:center;justify-content:space-between;padding:10px 12px;border-bottom:1px solid rgba(36,48,58,.09)}
    #signpostFilter .sf-title{font-weight:760;font-size:14px;letter-spacing:.01em}
    #signpostFilter .sf-count{font-size:10.5px;color:#77818a;margin-top:2px}
    #signpostFilter .sf-actions{display:flex;gap:6px;padding:8px 10px;border-bottom:1px solid rgba(36,48,58,.08)}
    #signpostFilter .sf-actions button{border:1px solid #d7d5cf;background:#fff;border-radius:8px;padding:4px 8px;font:inherit;font-size:11px;color:#4a545b;cursor:pointer;margin:0}
    #signpostFilter .sf-actions button:hover{background:#f2f0eb}
    #signpostFilter .sf-body{padding:6px 10px;overflow:auto;max-height:48vh}
    #signpostFilter .sf-row{display:flex;align-items:center;justify-content:space-between;gap:5px;padding:4px 0}
    #signpostFilter .sf-left{display:flex;align-items:center;gap:7px;min-width:0}
    #signpostFilter input{accent-color:#d97742}
    #signpostFilter .sf-label{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-weight:620}
    #signpostFilter .sf-num{font-size:10px;color:#879099;margin-left:auto}
    #signpostFilter .sf-toggle{border:0;background:transparent;color:#7b848a;cursor:pointer;padding:1px 4px;border-radius:6px;margin:0}
    #signpostFilter .sf-types{display:none;padding:2px 0 5px 24px}
    #signpostFilter .sf-types.open{display:block}
    #signpostFilter .sf-type{display:flex;align-items:center;gap:6px;padding:3px 0;font-size:11px;color:#5c666d}
    #signpostFilter .sf-foot{padding:8px 10px;border-top:1px solid rgba(36,48,58,.08);font-size:10px;color:#7c858b}
    .openup-wayfinding-card{display:flex;align-items:center;gap:10px;width:214px;min-height:54px;padding:9px 11px;border-radius:13px;background:rgba(251,250,247,.98);border:1px solid rgba(53,66,75,.12);box-shadow:0 8px 22px rgba(24,34,42,.16);font-family:system-ui,-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;color:#22313a;pointer-events:none}
    .openup-wayfinding-card .wf-accent{width:8px;height:34px;border-radius:999px;flex:none}
    .openup-wayfinding-card .wf-copy{min-width:0;line-height:1.12}
    .openup-wayfinding-card .wf-kicker{font-size:9px;font-weight:800;letter-spacing:.12em;text-transform:uppercase;margin-bottom:4px}
    .openup-wayfinding-card .wf-name{font-size:15px;font-weight:760;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
    .openup-wayfinding-card .wf-meta{font-size:10.5px;color:#747f87;margin-top:4px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
    .openup-wayfinding-card.major .wf-kicker{color:#d56e38}.openup-wayfinding-card.major .wf-accent{background:#d56e38}
    .openup-wayfinding-card.alt .wf-kicker{color:#5f7f92}.openup-wayfinding-card.alt .wf-accent{background:#6f96ac}
    .openup-route-arrow-wrap{background:transparent;border:0}
    .openup-route-arrow{display:block;filter:drop-shadow(0 2px 5px rgba(20,30,38,.18));transform-origin:center}
    .openup-route-arrow svg{display:block;overflow:visible}
    .openup-nearby-label{display:flex;align-items:center;gap:5px;pointer-events:none;white-space:nowrap;max-width:170px;padding:4px 7px 4px 5px;border-radius:999px;background:rgba(250,249,246,.9);border:1px solid rgba(38,50,60,.08);box-shadow:0 3px 10px rgba(30,40,48,.08);font:600 10.5px/1 system-ui,-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;color:#35434b}
    .openup-nearby-label .poi-dot{width:7px;height:7px;border-radius:50%;background:#e28a53;box-shadow:0 0 0 2px rgba(226,138,83,.16);flex:none}
    .openup-nearby-label.view .poi-dot{background:#70879a;box-shadow:0 0 0 2px rgba(112,135,154,.16)}
    .openup-nearby-label.water .poi-dot{background:#6c96ae;box-shadow:0 0 0 2px rgba(108,150,174,.16)}
    @media(max-width:800px){#signpostFilter{left:9px;right:auto;width:214px;top:66px;max-height:50vh}.openup-wayfinding-card{width:194px;min-height:50px}.openup-wayfinding-card .wf-name{font-size:14px}.openup-nearby-label{font-size:10px}}
    `;
  document.head.appendChild(style);

  const panel=document.createElement('div');
  panel.id='signpostFilter';
  panel.innerHTML=`
    <div class="sf-head"><div><div class="sf-title">Map details</div><div class="sf-count" id="signpostFilterCount">Loading…</div></div><button id="sfToggle" class="sf-toggle" title="Collapse">−</button></div>
    <div class="sf-actions"><button id="sfDefault">Default</button><button id="sfAll">All</button><button id="sfNone">None</button></div>
    <div class="sf-body" id="sfBody"></div>
    <div class="sf-foot">Wayfinding is shown only for selected details near the active route.</div>`;
  document.body.appendChild(panel);

  document.getElementById('sfDefault').onclick=()=>{
    selectedSignpostGroups=new Set(DEFAULT_SIGNPOST_GROUPS.filter(g=>signpostGroups.has(g)));
    selectedSignpostTypes=new Set();
    for(const r of osmSignposts)if(selectedSignpostGroups.has(r.group))selectedSignpostTypes.add(signpostTypeKey(r.group,r.type));
    renderSignpostFilter();renderOSMSignposts(lastSignpostBranches);
  };
  document.getElementById('sfAll').onclick=()=>{
    selectedSignpostGroups=new Set(DISPLAY_SIGNPOST_GROUPS.filter(g=>signpostGroups.has(g)));
    selectedSignpostTypes=new Set();
    for(const r of osmSignposts)if(selectedSignpostGroups.has(r.group))selectedSignpostTypes.add(signpostTypeKey(r.group,r.type));
    renderSignpostFilter();renderOSMSignposts(lastSignpostBranches);
  };
  document.getElementById('sfNone').onclick=()=>{
    selectedSignpostGroups.clear();selectedSignpostTypes.clear();
    renderSignpostFilter();renderOSMSignposts(lastSignpostBranches);
  };
  document.getElementById('sfToggle').onclick=()=>{
    const body=document.getElementById('sfBody');
    const hidden=body.style.display==='none';
    body.style.display=hidden?'block':'none';
    document.getElementById('sfToggle').textContent=hidden?'−':'+';
  };
}

function signpostField(r,names){
  for(const n of names){if(r?.[n]!==undefined&&r[n]!==null&&String(r[n]).trim()!=='')return r[n];}
  return null;
}
function normalizeSignpostRecords(payload){
  if(Array.isArray(payload))return payload;
  if(payload&&Array.isArray(payload.signposts))return payload.signposts;
  if(payload&&Array.isArray(payload.associations))return payload.associations;
  if(payload&&Array.isArray(payload.rows))return payload.rows;
  if(payload&&Array.isArray(payload.data))return payload.data;
  if(payload&&Array.isArray(payload.items))return payload.items;
  if(payload&&Array.isArray(payload.records))return payload.records;
  if(payload&&Array.isArray(payload.features))return payload.features;
  return [];
}
function normalizedDisplayGroup(type,sourceGroup){
  const t=String(type||'').toLowerCase();
  const g=String(sourceGroup||'').toUpperCase();
  if(t==='summit')return 'LANDSCAPE';
  if(['viewpoint','view','toposcope'].includes(t))return 'VIEWS';
  if(['waterbody','river','waterfall','dam','weir','spring','bay','beach','pier','harbour','slipway','quay','groyne','breakwater','shingle','sand','wetland','strait'].includes(t))return 'WATER';
  if(['shelter','wilderness_hut','hostel','camp_site','campsite','caravan_site'].includes(t))return 'SHELTER';
  if(DISPLAY_SIGNPOST_GROUPS.includes(g))return g;
  return null;
}
function normalizeSignpost(r,i){
  const lat=Number(signpostField(r,['lat','latitude','y','feature_lat','signpost_lat']));
  const lon=Number(signpostField(r,['lon','lng','longitude','x','feature_lon','signpost_lon']));
  if(!Number.isFinite(lat)||!Number.isFinite(lon))return null;
  const type=String(signpostField(r,['feature_type','type','signpost_type','category'])??'other').trim().toLowerCase()||'other';
  const sourceGroup=String(signpostField(r,['feature_group','group','signpost_group'])??'OTHER').trim().toUpperCase()||'OTHER';
  const group=normalizedDisplayGroup(type,sourceGroup);
  if(!group)return null;
  const name=String(signpostField(r,['name','feature_name','signpost_name','title'])??type.replace(/_/g,' ')).trim();
  const edgeRaw=signpostField(r,['nearest_pov_edge_id','pov_edge_id','nearest_edge_id','edge_id']);
  const nodeRaw=signpostField(r,['nearest_pov_node_id','pov_node_id','nearest_node_id','node_id']);
  const edgeId=edgeRaw===null?null:Number(edgeRaw);
  const nodeId=nodeRaw===null?null:Number(nodeRaw);
  if(edgeId!==null&&!Number.isFinite(edgeId))return null;
  const distanceRaw=signpostField(r,['nearest_pov_edge_distance_m','distance_to_pov_edge_m','pov_edge_distance_m','nearest_edge_distance_m','network_distance_m']);
  const networkDistance=distanceRaw===null?null:Number(distanceRaw);
  return {raw:r,index:i,id:String(signpostField(r,['signpost_id','id','feature_id','osm_id'])??i),name,type,group,sourceGroup,lat,lon,edgeId:Number.isFinite(edgeId)?edgeId:null,nodeId:Number.isFinite(nodeId)?nodeId:null,networkDistance:Number.isFinite(networkDistance)?networkDistance:null};
}
function signpostTypeKey(group,type){return `${group}::${type}`;}
function setupSignpostFilters(payload){
  const recs=normalizeSignpostRecords(payload).map(normalizeSignpost).filter(Boolean);
  osmSignposts=recs;signpostGroups=new Map();signpostTypes=new Map();
  for(const r of recs){
    signpostGroups.set(r.group,(signpostGroups.get(r.group)||0)+1);
    const key=signpostTypeKey(r.group,r.type);
    signpostTypes.set(key,(signpostTypes.get(key)||0)+1);
  }
  selectedSignpostGroups=new Set(DEFAULT_SIGNPOST_GROUPS.filter(g=>signpostGroups.has(g)));
  selectedSignpostTypes=new Set();
  for(const r of recs)if(selectedSignpostGroups.has(r.group))selectedSignpostTypes.add(signpostTypeKey(r.group,r.type));
  osmSignpostReady=true;
  renderSignpostFilter();
}
function groupLabel(g){return g.replace(/_/g,' ').replace(/\b\w/g,m=>m.toUpperCase());}
function typeLabel(t){
  if(t==='weir')return 'Burn';
  if(t==='summit')return 'Summit';
  if(t==='wilderness_hut')return 'Wilderness hut';
  if(t==='camp_site'||t==='campsite')return 'Campsite';
  if(t==='waterbody')return 'Loch / water';
  return t.replace(/_/g,' ').replace(/\b\w/g,m=>m.toUpperCase());
}
function humanDestinationName(r){
  const n=(r.name||typeLabel(r.type)).trim();
  if(r.type==='summit'&&!/^top of /i.test(n))return `Top of ${n}`;
  return n;
}
function setIndeterminate(box){
  if(!box)return;
  const group=box.dataset.group;
  const keys=[...signpostTypes.keys()].filter(k=>k.startsWith(`${group}::`));
  const selected=keys.filter(k=>selectedSignpostTypes.has(k));
  box.indeterminate=selected.length>0&&selected.length<keys.length;
}
function renderSignpostFilter(){
  const body=document.getElementById('sfBody'),count=document.getElementById('signpostFilterCount');
  if(!body||!count)return;
  if(!osmSignpostReady){count.textContent='Loading…';body.innerHTML='';return;}
  body.innerHTML=DISPLAY_SIGNPOST_GROUPS.filter(g=>signpostGroups.has(g)).map(g=>{
    const types=[...signpostTypes.keys()].filter(k=>k.startsWith(`${g}::`)).map(k=>k.split('::')[1]).sort();
    const checked=selectedSignpostGroups.has(g);
    const groupId=`sf-types-${g}`;
    return `<div class="sf-row"><label class="sf-left"><input type="checkbox" class="sf-group" data-group="${escapeHtmlSafe(g)}" ${checked?'checked':''}><span class="sf-label">${escapeHtmlSafe(groupLabel(g))}</span><span class="sf-num">${signpostGroups.get(g)}</span></label><button class="sf-toggle" data-open="${escapeHtmlSafe(g)}">+</button></div><div class="sf-types" id="${groupId}">${types.map(t=>{const key=signpostTypeKey(g,t);return `<label class="sf-type"><input type="checkbox" class="sf-type-check" data-group="${escapeHtmlSafe(g)}" data-type="${escapeHtmlSafe(t)}" ${selectedSignpostTypes.has(key)?'checked':''}><span>${escapeHtmlSafe(typeLabel(t))}</span><span class="sf-num">${signpostTypes.get(key)}</span></label>`;}).join('')}</div>`;
  }).join('');
  body.querySelectorAll('.sf-group').forEach(box=>box.onchange=()=>{
    const g=box.dataset.group;
    const keys=[...signpostTypes.keys()].filter(k=>k.startsWith(`${g}::`));
    if(box.checked){selectedSignpostGroups.add(g);keys.forEach(k=>selectedSignpostTypes.add(k));}
    else{selectedSignpostGroups.delete(g);keys.forEach(k=>selectedSignpostTypes.delete(k));}
    renderSignpostFilter();renderOSMSignposts(lastSignpostBranches);
  });
  body.querySelectorAll('.sf-type-check').forEach(box=>box.onchange=()=>{
    const key=signpostTypeKey(box.dataset.group,box.dataset.type),g=box.dataset.group;
    if(box.checked)selectedSignpostTypes.add(key);else selectedSignpostTypes.delete(key);
    const keys=[...signpostTypes.keys()].filter(k=>k.startsWith(`${g}::`));
    if(keys.length&&keys.every(k=>selectedSignpostTypes.has(k)))selectedSignpostGroups.add(g);else selectedSignpostGroups.delete(g);
    renderSignpostFilter();renderOSMSignposts(lastSignpostBranches);
  });
  body.querySelectorAll('[data-open]').forEach(btn=>btn.onclick=()=>{
    const el=document.getElementById(`sf-types-${btn.dataset.open}`);
    if(!el)return;const open=el.classList.toggle('open');btn.textContent=open?'−':'+';
  });
  body.querySelectorAll('.sf-group').forEach(setIndeterminate);
  const selectedCount=osmSignposts.filter(r=>selectedSignpost(r)).length;
  count.textContent=`${selectedCount.toLocaleString()} selected · ${osmSignposts.length.toLocaleString()} available`;
}
function clearOSMSignpostMarkers(){
  for(const m of osmSignpostMarkers)map.removeLayer(m);osmSignpostMarkers=[];
  for(const m of osmNearbyLabelMarkers)map.removeLayer(m);osmNearbyLabelMarkers=[];
  for(const l of osmWayfindingLines)map.removeLayer(l);osmWayfindingLines=[];
  for(const m of osmWayfindingArrows)map.removeLayer(m);osmWayfindingArrows=[];
}
function routeProgressByEdge(){
  const progress=new Map();let d=0;
  for(const step of routeSteps()){if(!progress.has(step.edge.id))progress.set(step.edge.id,d);d+=Number(step.edge?.w)||0;}
  return {progress,total:d};
}
function selectedSignpost(r){return selectedSignpostGroups.has(r.group)&&selectedSignpostTypes.has(signpostTypeKey(r.group,r.type));}
function pointAtDistanceOnCoords(coords,metres){return pointAlongCoords(coords,metres);}
function projectPointToEdge(feature,rEdge){
  const pts=rEdge?.coords||[];if(pts.length<2)return null;
  const lat0=(pts[0][1]+feature.lat)/2*Math.PI/180;const kx=111320*Math.cos(lat0),ky=111320;
  const px=feature.lon*kx,py=feature.lat*ky;let best=null,along=0,total=0;
  for(let i=1;i<pts.length;i++){
    const ax=pts[i-1][0]*kx,ay=pts[i-1][1]*ky,bx=pts[i][0]*kx,by=pts[i][1]*ky;
    const vx=bx-ax,vy=by-ay,len2=vx*vx+vy*vy;let t=len2?((px-ax)*vx+(py-ay)*vy)/len2:0;t=Math.max(0,Math.min(1,t));
    const qx=ax+t*vx,qy=ay+t*vy;const dx=px-qx,dy=py-qy,dist=Math.hypot(dx,dy);
    const seg=hav(pts[i-1],pts[i]);
    if(!best||dist<best.distance){best={distance:dist,alongOffset:total+t*seg,point:[pts[i-1][0]+t*(pts[i][0]-pts[i-1][0]),pts[i-1][1]+t*(pts[i][1]-pts[i-1][1])]};}
    total+=seg;
  }
  return best;
}
function branchTarget(branch,r){
  if(!branch?.edgeRuns?.length||r.edgeId===null)return null;
  const runIndex=branch.edgeRuns.findIndex(run=>run.id===r.edgeId);if(runIndex<0)return null;
  let before=0;for(let i=0;i<runIndex;i++)before+=Number(edgeMap.get(branch.edgeRuns[i].id)?.w)||0;
  const edge=edgeMap.get(r.edgeId);if(!edge)return null;
  const oriented=(edge.from===branch.edgeRuns[runIndex].from&&edge.to===branch.edgeRuns[runIndex].to)?edge.coords:[...edge.coords].reverse();
  const proj=projectPointToEdge(r,{...edge,coords:oriented});if(!proj)return null;
  return {along:before+proj.alongOffset,point:proj.point,distanceToBranch:proj.distance};
}
function branchPointAndBearing(branch,metres){
  const p=pointAlongCoords(branch.coords,Math.max(0,metres));
  if(!p)return null;
  const a=pointAlongCoords(branch.coords,Math.max(0,metres-12))||branch.coords[0];
  const b=pointAlongCoords(branch.coords,Math.min(branchLength(branch),metres+12))||branch.coords[branch.coords.length-1];
  return {point:p,bearing:initialBearing(a,b)};
}
function branchLength(branch){return (branch.edgeRuns||[]).reduce((s,run)=>s+(Number(edgeMap.get(run.id)?.w)||0),0);}
function initialBearing(a,b){
  const lon1=a[0]*Math.PI/180,lat1=a[1]*Math.PI/180,lon2=b[0]*Math.PI/180,lat2=b[1]*Math.PI/180;
  const y=Math.sin(lon2-lon1)*Math.cos(lat2),x=Math.cos(lat1)*Math.sin(lat2)-Math.sin(lat1)*Math.cos(lat2)*Math.cos(lon2-lon1);
  return (Math.atan2(y,x)*180/Math.PI+360)%360;
}
function directionalTypeScore(r){
  if(r.type==='summit')return 120;
  if(r.group==='HERITAGE')return 105;
  if(r.group==='SHELTER')return 92;
  if(r.group==='ROUTE_FEATURE'&&['bridge','ford','stepping_stones','guidepost'].includes(r.type))return 88;
  if(r.group==='ROUTE_FEATURE')return 64;
  return 0;
}
function isDirectionalCandidate(r){
  return directionalTypeScore(r)>0&&(r.networkDistance===null||r.networkDistance<=SIGNPOST_NEAR_ROUTE_M);
}
function renderOSMSignposts(branches=null){
  clearOSMSignpostMarkers();
  const activeBranches=Array.isArray(branches)?branches:lastSignpostBranches;
  if(!osmSignpostReady||current===null||!activeBranches?.length)return;

  const currentNode=nodeById(current);if(!currentNode)return;
  const directional=[];const nearby=[];
  const showNearby=false;


  for(const branch of activeBranches){
    if(!branch?.edgeRuns?.length)continue;
    const branchCandidates=[];const branchNear=[];
    for(const r of osmSignposts){
      if(!selectedSignpost(r)||r.edgeId===null)continue;
      const target=branchTarget(branch,r);if(!target)continue;
      const ahead=target.along;
      const edgeNear=target.distanceToBranch;
      const nearDistance=r.networkDistance===null?edgeNear:r.networkDistance;
      if(ahead<8||ahead>SIGNPOST_NEARBY_LOOKAHEAD_M)continue;
      const item={...r,ahead,target,nearDistance};
      if(isDirectionalCandidate(r)&&ahead<=SIGNPOST_DIRECTIONAL_LOOKAHEAD_M)branchCandidates.push(item);
      if((r.group==='VIEWS'||r.group==='LANDSCAPE'||r.group==='WATER'||r.group==='ROUTE_FEATURE'||r.group==='SHELTER'||r.group==='HERITAGE')&&nearDistance<=SIGNPOST_NEARBY_LABEL_M)branchNear.push(item);
    }
    branchCandidates.sort((a,b)=>directionalTypeScore(b)-directionalTypeScore(a)||a.ahead-b.ahead||a.name.localeCompare(b.name));
    if(branchCandidates.length)directional.push(branchCandidates[0]);
    nearby.push(...branchNear);
  }

  const seenDir=new Set();const dir=directional.filter(r=>{if(seenDir.has(r.id))return false;seenDir.add(r.id);return true;})
    .sort((a,b)=>directionalTypeScore(b)-directionalTypeScore(a)||a.ahead-b.ahead)
    .slice(0,SIGNPOST_MAX_DIRECTIONAL);

  dir.forEach((r,idx)=>{
    const branch=activeBranches.find(b=>b.edgeRuns?.some(run=>run.id===r.edgeId));if(!branch)return;
    const arrowDistance=Math.min(Math.max(52,r.ahead*0.34),Math.min(180,Math.max(52,branchLength(branch)-8)));
    const ab=branchPointAndBearing(branch,arrowDistance);if(!ab)return;
    const accent=idx===0?'#d56e38':'#6f96ac';
    const startDirection=branchPointAndBearing(branch,0);if(!startDirection)return;
    const pngRotation=(startDirection.bearing+45)%360;
    const pngArrowHTML=`<img class="openup-route-arrow" src="arrow.png" alt="" style="width:120px;height:84px;transform:rotate(${pngRotation}deg);transform-origin:center">`;
    const arrow=L.marker([currentNode.y,currentNode.x],{icon:L.divIcon({className:'openup-route-arrow-wrap',html:pngArrowHTML,iconSize:[120,84],iconAnchor:[60,42]}),zIndexOffset:1400,interactive:false}).addTo(map);
    osmWayfindingArrows.push(arrow);
    const targetX=L.marker([r.lat,r.lon],{icon:L.divIcon({className:'openup-route-arrow-wrap',html:'<span style="display:block;color:#e11d48;font:bold 34px/30px system-ui;text-shadow:-2px -2px 0 white,2px -2px 0 white,-2px 2px 0 white,2px 2px 0 white">×</span>',iconSize:[32,32],iconAnchor:[16,16]}),zIndexOffset:1600,interactive:false}).addTo(map);
    osmSignpostMarkers.push(targetX);


  });

  const uniqNear=new Map();for(const r of nearby){const old=uniqNear.get(r.id);if(!old||r.ahead<old.ahead)uniqNear.set(r.id,r);} 
  const near=[...uniqNear.values()].filter(r=>!seenDir.has(r.id)).sort((a,b)=>a.ahead-b.ahead||a.name.localeCompare(b.name));
  if(!showNearby)return;
  const usedPts=[];
  for(const r of near){
    if(usedPts.length>=SIGNPOST_MAX_NEARBY)break;
    const pos=map.latLngToContainerPoint([r.lat,r.lon]);
    if(usedPts.some(q=>Math.hypot(q.x-pos.x,q.y-pos.y)<48))continue;
    usedPts.push(pos);
    const kind=r.group==='VIEWS'?'view':(r.group==='WATER'?'water':'');
    const name=r.type==='summit'?humanDestinationName(r):r.name||typeLabel(r.type);
    const html=`<div class="openup-nearby-label ${kind}"><span class="poi-dot"></span><span>${escapeHtmlSafe(name)}</span></div>`;
    const marker=L.marker([r.lat,r.lon],{icon:L.divIcon({className:'openup-nearby-wrap',html,iconSize:[1,1],iconAnchor:[0,10]}),zIndexOffset:1180,interactive:false}).addTo(map);
    osmNearbyLabelMarkers.push(marker);
    if(r.nearDistance>35){
      const branch=activeBranches.find(b=>b.edgeRuns?.some(run=>run.id===r.edgeId));
      if(branch){
        const target=branchTarget(branch,r);if(target){
          const lead=L.polyline([[target.point[1],target.point[0]],[r.lat,r.lon]],{color:'#85929b',weight:1,opacity:.22,dashArray:'2 6',interactive:false}).addTo(map);
          osmWayfindingLines.push(lead);
        }
      }
    }
  }
}

function clearChoices(){
  for(const l of choiceLayers)map.removeLayer(l);
  choiceLayers=[];
  choiceFlowLayers=[];
  clearKnownWalkMarkers();
  clearOSMSignpostMarkers();
  lastSignpostBranches=[];
  renderKnownWalkList([]);
}
function clipCoords(coords, maxMetres){
  if(!coords || coords.length<2 || maxMetres<=0)return [];
  const out=[[coords[0][0],coords[0][1]]];
  let used=0;
  for(let i=1;i<coords.length;i++){
    const a=coords[i-1], b=coords[i];
    const seg=hav(a,b);
    if(used+seg<=maxMetres){
      out.push([b[0],b[1]]); used+=seg; continue;
    }
    const remain=maxMetres-used;
    if(seg>0){
      const t=remain/seg;
      out.push([a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t]);
    }
    break;
  }
  return out;
}
function drawChoices(){
  clearChoices();
  if(current===null)return;

  const committedIds=new Set(routeSteps().map(s=>s.edge.id));
  const lastStep=routeSteps().at(-1);
  const incomingId=lastStep?.edge.id ?? null;

  const branchResults=[];

  const addChoiceLine=(coords,endNode,edgePath,edgeRuns)=>{
    branchResults.push({coords:[...coords],endNode,edgePath:[...edgePath],edgeRuns:[...(edgeRuns||[])]});
    if(coords.length<2)return;
    const latlngs=coords.map(p=>[p[1],p[0]]);
    const base=L.polyline(latlngs,{
      color:BLUE,weight:4,opacity:.20,lineCap:'round',lineJoin:'round',
      smoothFactor:0,interactive:true
    }).addTo(map);
    const flow=L.polyline(latlngs,{
      color:BLUE,weight:2,opacity:.62,dashArray:'2 20',
      lineCap:'round',lineJoin:'round',smoothFactor:0,interactive:true
    }).addTo(map);
    base.bringToFront();flow.bringToFront();
    const activate=()=>clickNode(endNode);
    base.on('click',activate);flow.on('click',activate);
    choiceLayers.push(base,flow);
    choiceFlowLayers.push(flow);
  };

  // Build a continuous geometric path from the current position through
  // real edge coordinates. We do not draw a separate segment per node.
  const walkBranch=(node,dist,coords,used,edgePath,edgeRuns)=>{
    const nexts=(adj.get(node)||[]).filter(e=>{
      if(committedIds.has(e.id))return false;
      if(edgePath.includes(e.id))return false;
      if(used.has(e.to))return false;
      // Never immediately preview back along the edge we just came from.
      if(edgePath.length===0 && e.id===incomingId)return false;
      return true;
    });

    if(!nexts.length){
      if(coords.length>1)addChoiceLine(coords,node,edgePath);
      return;
    }

    for(const e of nexts){
      const edge=edgeMap.get(e.id);
      if(!edge?.coords?.length)continue;

      let c=(edge.from===node && edge.to===e.to)
        ? edge.coords
        : [...edge.coords].reverse();

      // Join the actual geometry exactly at the shared coordinate.
      // This avoids the visual "snap" caused by drawing each edge separately.
      const nc=coords.slice();
      if(nc.length && c.length){
        const a=nc[nc.length-1];
        const b=c[0];
        if(Math.abs(a[0]-b[0])<1e-10 && Math.abs(a[1]-b[1])<1e-10){
          c=c.slice(1);
        }
      }
      nc.push(...c);

      const nd=dist+(Number(e.w)||0);
      const nu=e.to;
      const nused=new Set(used);
      nused.add(nu);
      const npath=[...edgePath,e.id];

      // Always draw the accumulated geometry as one continuous line.
      // If we've reached 500m, stop at this actual network node.
      const nruns=[...(edgeRuns||[]),{id:e.id,from:node,to:nu}];

      if(nd>=CHOICE_RADIUS_M){
        addChoiceLine(nc,nu,npath,nruns);
        continue;
      }

      // If this is a junction, the shared part is shown once for each
      // resulting branch, then each branch continues independently.
      walkBranch(nu,nd,nc,nused,npath,nruns);
    }
  };

  const initial=(adj.get(current)||[]).filter(e=>{
    if(committedIds.has(e.id))return false;
    if(e.id===incomingId)return false;
    return true;
  });

  for(const e of initial){
    const edge=edgeMap.get(e.id);
    if(!edge?.coords?.length)continue;

    let c=(edge.from===current && edge.to===e.to)
      ? edge.coords
      : [...edge.coords].reverse();

    const used=new Set([current,e.to]);
    const dist=Number(e.w)||0;

    const initialEdge=edgeMap.get(e.id);
    const initialRun={id:e.id,from:initialEdge.from===current?current:initialEdge.to,to:initialEdge.from===current?initialEdge.to:current};
    if(dist>=CHOICE_RADIUS_M){
      addChoiceLine(c,e.to,[e.id],[initialRun]);
    }else{
      walkBranch(e.to,dist,c,used,[e.id],[initialRun]);
    }
  }

  if(!choiceLayers.length){
    document.getElementById('info').textContent='No onward network choices from here.';
  }

  lastSignpostBranches=branchResults;
  renderKnownWalkSignposts(branchResults);
  renderOSMSignposts(branchResults);
}

function setNodeStyle(id,on){
  const m=nodeLayers.get(id);if(!m)return;
  const isStart=starts.has(id),isCurrent=id===current;
  m.setRadius(isStart?9:(isCurrent?9:5));
  m.setStyle({
    color:isStart?'#0a7f2e':(isCurrent?ORANGE:'#6b7280'),
    fillColor:isStart?'#22c55e':(isCurrent?ORANGE:'#ffffff'),
    fillOpacity:isStart||isCurrent?1:.9,
    weight:isStart||isCurrent?3:1.5
  });
}
function refreshNodeStyles(){
  for(const n of graph.nodes)setNodeStyle(n.id,false);
}
function start(id){
  current=id;startNode=id;routeSegments=[];
  refreshNodeStyles();setNodeStyle(id,true);
  drawRoute();drawChoices();updateStats();
  document.getElementById('info').textContent='You are here. Blue routes show at least 500 m of available network, ending at the next node.';
  setupDragMarker();
}
function clickNode(id){
  if(current===null){
    if(starts.has(id))start(id);
    else document.getElementById('info').textContent='Choose a green start point.';
    return;
  }
  if(id===current)return;
  const r=dijkstra(current,id);
  if(!r){document.getElementById('info').textContent='No route between these nodes.';return;}
  routeSegments.push({from:current,to:id,steps:r.steps,metres:r.metres});
  current=id;
  refreshNodeStyles();setNodeStyle(id,true);
  drawRoute();drawChoices();updateStats();setupDragMarker();
  document.getElementById('info').textContent='Route built. Drag the orange endpoint onto another path to change the last section.';
}
function setupDragMarker(){
  if(dragMarker)map.removeLayer(dragMarker);
  if(current===null||!routeSegments.length)return;
  const n=nodeById(current);
  if(!n)return;
  const icon=L.divIcon({className:'drag-handle',html:'<div></div>',iconSize:[24,24],iconAnchor:[12,12]});
  dragMarker=L.marker([n.y,n.x],{icon,draggable:true,zIndexOffset:2000}).addTo(map);
  dragMarker.on('dragend',()=>{
    const ll=dragMarker.getLatLng();
    let best=null,bestD=Infinity;
    for(const n of graph.nodes){
      const dd=hav([ll.lng,ll.lat],[n.x,n.y]);
      if(dd<bestD){bestD=dd;best=n;}
    }
    if(!best||bestD>150){
      document.getElementById('info').textContent='Drop closer to a network track (within 150 m).';
      setupDragMarker();return;
    }
    const last=routeSegments[routeSegments.length-1];
    const r=dijkstra(last.from,best.id);
    if(!r){
      document.getElementById('info').textContent='That track cannot be reached from the previous route point.';
      setupDragMarker();return;
    }
    routeSegments[routeSegments.length-1]={from:last.from,to:best.id,steps:r.steps,metres:r.metres};
    current=best.id;
    refreshNodeStyles();setNodeStyle(current,true);
    drawRoute();drawChoices();updateStats();setupDragMarker();
    document.getElementById('info').textContent=`Route changed to the new track (${Math.round(bestD)} m snap).`;
  });
}
function downloadGPX(name,coords){
  if(!coords.length){document.getElementById('info').textContent='Nothing to export yet.';return;}
  const esc=s=>String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
  const trkpts=coords.map(([lat,lon])=>`<trkpt lat="${lat}" lon="${lon}"></trkpt>`).join('');
  const gpx=`<?xml version="1.0" encoding="UTF-8"?>
<gpx version="1.1" creator="Arran POV Builder" xmlns="http://www.topografix.com/GPX/1/1">
  <trk><name>${esc(name)}</name><trkseg>${trkpts}</trkseg></trk>
</gpx>`;
  const blob=new Blob([gpx],{type:'application/gpx+xml'});
  const url=URL.createObjectURL(blob),a=document.createElement('a');
  a.href=url;a.download=`${name.toLowerCase().replace(/[^a-z0-9]+/g,'-').replace(/^-|-$/g,'')}.gpx`;
  document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),1000);
}
function endWalk(){
  if(current===null){document.getElementById('info').textContent='Start a walk first.';return;}
  downloadGPX('arran-walk',routeCoordinates());
  current=null;clearChoices();if(dragMarker){map.removeLayer(dragMarker);dragMarker=null}
  refreshNodeStyles();updateStats();
  document.getElementById('info').textContent='Walk ended and GPX downloaded.';
}
function returnHome(){
  if(current===null||startNode===null){document.getElementById('info').textContent='Start a walk first.';return;}
  const r=returnRoute();
  if(!r){document.getElementById('info').textContent='No route back to the starting point.';return;}
  const full=[...routeCoordinates()];
  const returnCoords=[];
  for(const step of r.steps){
    const e=edgeMap.get(step.edge.id);
    let c=(e.from===step.from&&e.to===step.to)?e.coords:[...e.coords].reverse();
    const ll=c.map(p=>[p[1],p[0]]);
    if(returnCoords.length&&ll.length)ll.shift();
    returnCoords.push(...ll);
  }
  const combined=full.length?full.concat(returnCoords):returnCoords;
  downloadGPX('arran-walk-return-home',combined);
  current=startNode;
  routeSegments.push({from:(routeSegments.length?routeSegments[routeSegments.length-1].to:startNode),to:startNode,steps:r.steps,metres:r.metres});
  drawRoute();clearChoices();updateStats();
  document.getElementById('info').textContent='Returned home and GPX downloaded.';
}
function clearWalk(){
  current=null;startNode=null;routeSegments=[];
  if(routeLayer){map.removeLayer(routeLayer);routeLayer=null}
  clearChoices();if(dragMarker){map.removeLayer(dragMarker);dragMarker=null}
  refreshNodeStyles();updateStats();document.getElementById('info').textContent='Cleared.';
}

let choiceFlowOffset=0;
function animateChoiceFlow(){
  choiceFlowOffset-=0.45;
  for(const layer of choiceFlowLayers){
    if(layer && layer._path) layer._path.style.strokeDashoffset=`${choiceFlowOffset}px`;
  }
  requestAnimationFrame(animateChoiceFlow);
}
requestAnimationFrame(animateChoiceFlow);

function updateNodeVisibility(){
  if(!graph)return;

  const z=map.getZoom();
  const candidates=[];

  for(const n of graph.nodes){
    const m=nodeLayers.get(n.id);
    if(!m)continue;

    if(starts.has(n.id)){
      candidates.push({n,m,force:true});
      continue;
    }

    const degree=n._degree ?? (adj.get(n.id)||[]).length;

    let show=false;
    if(z>=14){
      show=true;
    }else if(z>=13){
      show=(degree!==2);
    }else{
      show=(degree>=3);
    }

    if(show)candidates.push({n,m,force:false});
  }

  // Hide all ordinary node markers first.
  for(const n of graph.nodes){
    const m=nodeLayers.get(n.id);
    if(m){
      m.setStyle({opacity:0,fillOpacity:0});
      m.options.interactive=false;
    }
  }

  // Starts are always individually visible.
  for(const c of candidates.filter(x=>x.force)){
    c.m.setStyle({opacity:1,fillOpacity:1});
    c.m.options.interactive=true;
  }

  const normal=candidates.filter(x=>!x.force);

  if(z>=14){
    // Close enough for precise editing: no visual clustering.
    for(const c of normal){
      c.m.setStyle({opacity:1,fillOpacity:1});
      c.m.options.interactive=true;
    }
    return;
  }

  // Cluster in screen space, not geographic metres. This means the visual
  // density stays sensible at different map scales.
  const clusterPx = z<13 ? 30 : 22;
  const points=normal.map(c=>({
    ...c,
    pt:map.latLngToLayerPoint([c.n.y,c.n.x])
  }));

  const used=new Set();

  for(let i=0;i<points.length;i++){
    if(used.has(i))continue;

    const group=[i];
    used.add(i);

    for(let j=i+1;j<points.length;j++){
      if(used.has(j))continue;

      const dx=points[j].pt.x-points[i].pt.x;
      const dy=points[j].pt.y-points[i].pt.y;

      if(Math.hypot(dx,dy)<=clusterPx){
        group.push(j);
        used.add(j);
      }
    }

    // One representative marker for the cluster: prefer the node with the
    // highest degree because it is the most meaningful decision point.
    let rep=group[0];
    for(const idx of group){
      if((points[idx].n._degree||0)>(points[rep].n._degree||0)){
        rep=idx;
      }
    }

    const c=points[rep];
    c.m.setStyle({opacity:1,fillOpacity:1});
    c.m.options.interactive=true;
  }
}
map.on('zoomend',updateNodeVisibility);

function fetchRequiredJSON(path){return fetch(path).then(r=>{if(!r.ok)throw new Error(`${path} ${r.status}`);return r.json();});}
function fetchJSONOptional(path,fallback){
  return fetch(path).then(r=>{if(!r.ok)throw new Error(`${path} ${r.status}`);return r.json();}).catch(()=>fallback);
}

injectSignpostUI();

fetchRequiredJSON('arran_pov.json').then(d=>{
  graph=d;
  for(const s of d.starts||[])starts.add(s);
  for(const e of d.edges){
    edgeMap.set(e.id,e);addAdj(e.from,e.to,e.w,e.id);addAdj(e.to,e.from,e.w,e.id);
    layers.push(L.polyline(e.coords.map(p=>[p[1],p[0]]),{color:GREY,weight:2,opacity:.38}).addTo(map));
  }
  for(const n of d.nodes){
    const isStart=starts.has(n.id);
    const degree=(adj.get(n.id)||[]).length;
    n._degree=degree;
    const m=L.circleMarker([n.y,n.x],{radius:isStart?9:5,color:isStart?'#0a7f2e':'#6b7280',fillColor:isStart?'#22c55e':'#ffffff',fillOpacity:isStart?1:.9,weight:isStart?3:1.5,opacity:isStart?1:(degree===2?0:1),interactive:isStart||degree!==2}).addTo(map);
    m.on('click',()=>clickNode(n.id));nodeLayers.set(n.id,m);
  }
  updateNodeVisibility();
  if(layers.length)map.fitBounds(L.featureGroup(layers).getBounds());
  document.getElementById('stats').textContent=`${d.nodes.length} nodes • ${d.edges.length} edges • ${d.starts.length} starts`;
  updateStats();
  renderOSMSignposts();
}).catch(err=>{
  console.error(err);
  document.getElementById('info').textContent='Could not load arran_pov.json.';
});

fetchJSONOptional('arran_signpost_network_associations.json',null).then(payload=>{
  if(payload){
    setupSignpostFilters(payload);
    renderOSMSignposts(lastSignpostBranches);
  }else{
    osmSignpostReady=false;
    renderSignpostFilter();
    const c=document.getElementById('signpostFilterCount');
    if(c)c.textContent='Association file not found';
  }
});

document.getElementById('fit').onclick=()=>{if(layers.length)map.fitBounds(L.featureGroup(layers).getBounds)};
document.getElementById('clear').onclick=clearWalk;
document.getElementById('end').onclick=endWalk;
document.getElementById('home').onclick=returnHome;
