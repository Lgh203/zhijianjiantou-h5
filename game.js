/* H5 reconstruction: original map paths/configuration and existing game assets.
 * Forward-ray clearance is inferred from the original maps' solvable topology.
 * Three-heart mistakes, free hints/retries and browser controls are H5 rules.
 * No Android SDK, account, advertising or payment code is included. */
const WIDTH=360,HEIGHT=640;
const BOARD={x:12,y:104,width:336,height:426};
const BLOCK_MS=360,WIN_DELAY=400;
const clamp=(v,min,max)=>Math.min(max,Math.max(min,v));
const lerp=(a,b,t)=>a+(b-a)*t;
const key=(x,y)=>`${x},${y}`;

function createLevelState(map,{level=1,mode='campaign',index=0}={}) {
  const occupancy=new Map();
  const arrows=map.Arrows.map((raw,id)=>{
    const points=raw.Indices.map(i=>({x:i%map.XSize,y:Math.floor(i/map.XSize)}));
    const arcDistances=[0];
    for(let i=1;i<points.length;i++)arcDistances.push(arcDistances[i-1]+Math.hypot(points[i].x-points[i-1].x,points[i].y-points[i-1].y));
    points.forEach(point=>{const k=key(point.x,point.y);if(!occupancy.has(k))occupancy.set(k,new Set());occupancy.get(k).add(id);});
    return {id,indices:raw.Indices.slice(),points,head:{x:raw.X,y:raw.Y},direction:{x:raw.Dx,y:raw.Dy},arcDistances,pathLength:arcDistances.at(-1),status:'idle',animationStart:0,animationDuration:0,travel:0,exitDistance:0,blockedBy:[]};
  });
  return {level,mode,index,XSize:map.XSize,YSize:map.YSize,arrows,occupancy,lives:3,moves:0,removed:0,paused:false,won:false,failed:false,winAt:0,failAt:0,hintId:-1,hintUntil:0};
}

/** Other stationary arrows along the head's forward ray; self never blocks. */
function forwardBlockers(state,id) {
  const arrow=state.arrows[id];if(!arrow)return [];
  const result=new Set();
  let x=arrow.head.x+arrow.direction.x,y=arrow.head.y+arrow.direction.y;
  while(x>=0&&x<state.XSize&&y>=0&&y<state.YSize) {
    for(const other of state.occupancy.get(key(x,y))||[]) {
      const status=state.arrows[other].status;
      if(other!==id&&status!=='removed'&&status!=='moving')result.add(other);
    }
    x+=arrow.direction.x;y+=arrow.direction.y;
  }
  return [...result];
}

/** Distance is measured in original grid units, head-to-tail; negative = exit ray. */
function samplePath(arrow,distance) {
  if(distance<0)return {x:arrow.head.x-arrow.direction.x*distance,y:arrow.head.y-arrow.direction.y*distance};
  if(distance>=arrow.pathLength)return {...arrow.points.at(-1)};
  let low=0,high=arrow.arcDistances.length-1;
  while(high-low>1){const middle=(low+high)>>1;if(arrow.arcDistances[middle]<=distance)low=middle;else high=middle;}
  const start=arrow.points[low],end=arrow.points[low+1],length=arrow.arcDistances[low+1]-arrow.arcDistances[low];
  const t=length?(distance-arrow.arcDistances[low])/length:0;
  return {x:lerp(start.x,end.x,t),y:lerp(start.y,end.y,t)};
}

/** The tail follows its own track: it does not sweep the entire bent shape. */
function movingPath(arrow,travel) {
  const result=[samplePath(arrow,-travel)];
  for(let i=0;i<arrow.points.length;i++){
    const bodyDistance=arrow.arcDistances[i]+travel;
    if(bodyDistance>0&&bodyDistance<arrow.pathLength)result.push({...arrow.points[i]});
  }
  result.push(samplePath(arrow,arrow.pathLength-travel));return result;
}

function segmentDistance(point,a,b) {
  const dx=b.x-a.x,dy=b.y-a.y,length=dx*dx+dy*dy;
  const t=length?clamp(((point.x-a.x)*dx+(point.y-a.y)*dy)/length,0,1):0;
  return Math.hypot(point.x-(a.x+dx*t),point.y-(a.y+dy*t));
}

if(typeof document!=='undefined') initializeBrowser();

function initializeBrowser() {
  const $=id=>document.getElementById(id);
  const canvas=$('game-canvas'),mainCtx=canvas.getContext('2d',{alpha:false});
  let ctx=mainCtx;
  const cache=document.createElement('canvas');let cacheDirty=true;
  const images=new Map(),tints=new Map(),mapCache=new Map();
  const STORAGE='zhijian_arrow_h5_v1.';
  const read=(name,fallback)=>{try{return localStorage.getItem(STORAGE+name)??fallback;}catch{return fallback;}};
  const save=(name,value)=>{try{localStorage.setItem(STORAGE+name,String(value));}catch{/* Storage is optional in privacy mode. */}};
  const defaults=()=>({unlocked:1,currentLevel:1,completedCampaign:[],completedChallenges:[],lastChallenge:0});
  let progress=defaults();try{progress={...progress,...JSON.parse(read('progress','{}'))};}catch{}
  progress.unlocked=clamp(Number(progress.unlocked)||1,1,40);progress.currentLevel=clamp(Number(progress.currentLevel)||1,1,progress.unlocked);
  if(!Array.isArray(progress.completedCampaign))progress.completedCampaign=[];
  if(!Array.isArray(progress.completedChallenges))progress.completedChallenges=[];
  let consentAccepted=read('consent','false')==='true',musicEnabled=read('music','true')!=='false',sfxEnabled=read('sfx','true')!=='false',gridEnabled=read('grid','true')!=='false';
  let ready=false,scene='loading',catalog={levels:[],challenges:[]},state=null,currentEntry=null;
  let challengePage=0,legalReturn='home',lastFrame=performance.now(),gameTime=0,toastUntil=0,loadGeneration=0,loadRetry=()=>location.reload();
  let camera={zoom:1,panX:0,panY:0,baseCell:18,centerX:180,centerY:BOARD.y+BOARD.height/2};
  const bgm=$('bgm');bgm.volume=.4;
  let audioContext=null,audioEnabled=false,sfxLoading=false,sfxPlayed=0;
  const buffers=new Map(),soundNames=['LevelIncrease','Mistake','Tap','Complete','Arrow','LevelFail'];
  const pointers=new Map();let pinch=null;
  const fullScreens=['loading','home','campaign','challenge','settings','exit'];
  const modalScreens=['consent','legal','paused','won','failed','confirm'];
  const modalIds={paused:'pause-screen',won:'win-screen',failed:'fail-screen'};

  function status(text){$('accessible-status').textContent=text;}
  function notify(text){$('toast').textContent=text;$('toast').hidden=false;toastUntil=performance.now()+2400;status(text);}
  function saveProgress(){save('progress',JSON.stringify(progress));}
  function sceneToId(name){return modalIds[name]||`${name}-screen`;}
  function setScene(name) {
    scene=name;
    for(const value of fullScreens.concat(modalScreens))$(sceneToId(value)).hidden=value!==name;
    const gameVisible=!!state&&['game','paused','won','failed'].includes(name);
    $('game-ui').hidden=!gameVisible;
    if(name==='game')for(const value of fullScreens.concat(modalScreens))$(sceneToId(value)).hidden=true;
    if(['home','settings'].includes(name))refreshHome();
    syncMusic();
  }
  function syncMusic() {
    if(audioEnabled&&consentAccepted&&musicEnabled&&!document.hidden&&['home','campaign','challenge','settings','game','won'].includes(scene))bgm.play().catch(()=>{});
    else bgm.pause();
  }
  function unlockAudio() {
    audioEnabled=true;
    // HTMLAudio.play must run synchronously in the actual click/touch stack,
    // not after waiting for AudioContext.resume (important on iOS browsers).
    syncMusic();
    const AudioCtx=window.AudioContext||window.webkitAudioContext;
    if(!AudioCtx)return;
    audioContext??=new AudioCtx();
    if(audioContext.state==='suspended')audioContext.resume().catch(()=>{});
    if(!sfxLoading){sfxLoading=true;for(const name of soundNames)fetch(`./assets/audio/${name}.wav`).then(response=>{
      if(!response.ok)throw Error(`音效加载失败 (${response.status})`);return response.arrayBuffer();
    }).then(bytes=>audioContext.decodeAudioData(bytes)).then(buffer=>buffers.set(name,buffer)).catch(error=>console.warn(error.message));}
  }
  function playSound(name,volume=.65) {
    if(!audioEnabled||!sfxEnabled||!audioContext||audioContext.state!=='running')return;
    const buffer=buffers.get(name);if(!buffer)return;
    const source=audioContext.createBufferSource(),gain=audioContext.createGain();source.buffer=buffer;gain.gain.value=volume;
    source.connect(gain).connect(audioContext.destination);source.start();sfxPlayed++;
  }
  function refreshSettings() {
    for(const [id,value] of [['music-toggle',musicEnabled],['sound-toggle',sfxEnabled],['grid-toggle',gridEnabled]]){
      $(id).querySelector('strong').textContent=value?'开启':'关闭';$(id).setAttribute('aria-pressed',String(value));
    }
    $('pause-music').textContent=`音乐：${musicEnabled?'开启':'关闭'}`;
  }
  function toggleMusic(){musicEnabled=!musicEnabled;save('music',musicEnabled);refreshSettings();unlockAudio();}
  function refreshHome() {
    $('progress-label').textContent=`主线关卡 ${progress.currentLevel}`;
    $('challenge-status').textContent=challengesUnlocked()?`${catalog.challenges.length} 张原地图`:'完成主线第3关解锁';
    refreshSettings();
  }
  function challengesUnlocked(){return progress.completedCampaign.includes(3);}
  function goHome(){pointers.clear();pinch=null;setScene('home');}

  const legal={
    privacy:`<p>更新日期：2026年10月11日<br>运营主体：南京郁真信息科技有限公司</p><h3>一、服务范围</h3><p>本政策适用于《指尖箭头大挑战》H5重做版网页试玩。当前无需注册，不接入Android账号、广告、支付或联运SDK，不提供充值、提现或付费服务。</p><h3>二、本地存储</h3><p>主线关卡解锁、已完成主线和扩展挑战、当前关卡、音乐音效与点阵设置、隐私同意记录保存在同一网站的当前浏览器localStorage中。游戏不主动上传这些存档，不进行云同步。重新打开会重新开始保存的关卡，不保存正在移动中的棋盘。</p><p>清理网站数据、隐私浏览模式、更换设备、浏览器或网站地址可能导致本地数据丢失。在设置中可以仅清除本游戏进度；在浏览器网站设置中可以清除所有本站记录以撤回同意。</p><h3>三、网络与静态托管</h3><p>网页代码、图片、音乐、关卡目录和正在游玩的关卡文件需要通过网络加载。正式试玩采用GitHub Pages静态托管。托管服务可能记录访问IP、请求时间、User-Agent和必要技术日志，其处理方式以该服务自身政策为准。本游戏不能被理解为完全离线或没有服务器日志。</p><h3>四、权限及第三方SDK</h3><p>本网页不主动调用定位、摄像头、麦克风、通讯录或传感器，不要求手机号或实名认证。音乐与音效在真实用户点击后启用，您可随时关闭。浏览器触摸、鼠标和双指缩放仅用于操作棋盘。</p><h3>五、未成年人和联系我们</h3><p>未成年人请在监护人指导下体验，合理安排游戏时间。不同意可退出试玩。关于网页服务或隐私事项，可通过游戏发布方提供的客服渠道联系运营主体。若未来加入账号、广告、支付或其他SDK，将另行说明并更新政策。</p>`,
    agreement:`<p>更新日期：2026年10月11日<br>运营主体：南京郁真信息科技有限公司</p><h3>一、H5重做版</h3><p>本网页使用现有工程的箭头路径、素材与可恢复主线配置重新实现浏览器玩法，不声称恢复原Unity/C#完整执行源码。前40关使用可恢复的原主线顺序；扩展挑战图库与主线独立，其排列属于网页重建排列，不称为原版后续主线。</p><h3>二、网页玩法</h3><p>点击箭头，当箭头头部前方射线未被其他箭头占格阻挡时，箭头沿自身路径抽出离场。碰撞扣一颗心，三颗心用尽失败；重试与提示均免费，不需要看广告。这些碰撞、提示与网页控制是H5重做规则。</p><p>棋盘可拖动、双指或滚轮缩放，也可以用放大、缩小与复位按钮操作。观察空间后再点击，移走全部箭头即可完成。不可解的已知互锁地图不纳入可玩扩展图库。</p><h3>三、服务和数据</h3><p>试玩无需账号，不提供付费、提现、现金奖励、广告变现或AndroidSDK功能。游戏文件加载需网络。进度只保存在当前网站的本浏览器中；换浏览器、隐私模式、清除记录或换网站地址可能导致数据丢失，不承诺云端找回。</p><h3>四、健康游戏和权利</h3><p>请合理安排时间，未成年人应由监护人指导。不得利用网页从事违法行为或破坏服务。画面、音频和关卡等内容的使用应遵守有关权利和授权范围。</p><h3>五、服务边界</h3><p>网页试玩不等于已通过应用商店审核或所有实体手机机型验证。浏览器能力、网络和静态托管状态可能影响体验。后续若新增账号、广告、支付等功能，将另行更新说明。</p>`,
    howto:`<h3>让箭头找到出口</h3><p>点中一根箭头，它会沿着箭头头部的方向离场。弯折部分会沿自身路径依次抽出，不会整根横扫棋盘。</p><p>如果头部前方还有别的箭头挡住，点击会扣一颗心。先移走挡路箭头。三颗心用尽可以免费重试。</p><h3>放大观察</h3><p>拖动棋盘可以移动视野；双指或滚轮缩放。也可使用＋、−和复位按钮。拖动与点击会自动区分。</p><h3>提示与关卡</h3><p>提示会高亮当前可以离场的箭头，不自动替您完成。完成主线第3关即可开启原地图扩展挑战图库，与40关主线独立。</p>`
  };
  function openLegal(kind) {
    legalReturn=scene;setScene('legal');$('legal-title').textContent=kind==='agreement'?'用户协议':kind==='howto'?'玩法说明':'隐私政策';
    $('legal-content').innerHTML=legal[kind]||legal.privacy;$('legal-content').scrollTop=0;
  }
  document.querySelectorAll('[data-legal]').forEach(button=>button.addEventListener('click',event=>{event.preventDefault();openLegal(button.dataset.legal);}));
  $('legal-close').addEventListener('click',()=>setScene(legalReturn));
  $('how-to-button').addEventListener('click',()=>openLegal('howto'));
  $('agree-button').addEventListener('click',()=>{consentAccepted=true;save('consent',true);setScene('home');unlockAudio();});
  $('decline-button').addEventListener('click',()=>setScene('exit'));
  $('return-button').addEventListener('click',()=>setScene(consentAccepted?'home':'consent'));
  $('exit-button').addEventListener('click',()=>setScene('exit'));
  $('music-toggle').addEventListener('click',toggleMusic);$('pause-music').addEventListener('click',toggleMusic);
  $('sound-toggle').addEventListener('click',()=>{sfxEnabled=!sfxEnabled;save('sfx',sfxEnabled);refreshSettings();unlockAudio();playSound('Tap');});
  $('grid-toggle').addEventListener('click',()=>{gridEnabled=!gridEnabled;save('grid',gridEnabled);refreshSettings();cacheDirty=true;});
  $('reset-progress').addEventListener('click',()=>setScene('confirm'));
  $('cancel-reset').addEventListener('click',()=>setScene('settings'));
  $('confirm-reset').addEventListener('click',()=>{
    try{localStorage.removeItem(STORAGE+'progress');}catch{}progress=defaults();state=null;setScene('settings');notify('本游戏进度已清除，音乐设置保持不变');
  });
  $('loading-retry').addEventListener('click',()=>loadRetry());
  $('start-button').addEventListener('click',()=>{if(!consentAccepted){setScene('consent');return;}unlockAudio();loadLevel('campaign',progress.currentLevel-1);});
  $('campaign-button').addEventListener('click',()=>{renderCampaign();setScene('campaign');unlockAudio();});
  $('settings-tab').addEventListener('click',()=>{setScene('settings');unlockAudio();});
  $('home-tab').addEventListener('click',goHome);
  document.querySelectorAll('.back-home').forEach(button=>button.addEventListener('click',goHome));
  $('challenge-tab').addEventListener('click',()=>{
    if(!challengesUnlocked()){notify('完成主线第3关后，开启扩展挑战图库');return;}
    renderChallenges();setScene('challenge');unlockAudio();
  });
  $('challenge-prev').addEventListener('click',()=>{challengePage--;renderChallenges();});
  $('challenge-next').addEventListener('click',()=>{challengePage++;renderChallenges();});

  function renderCampaign() {
    const grid=$('campaign-grid');grid.replaceChildren();
    catalog.levels.forEach((entry,index)=>{
      const button=document.createElement('button');button.className='level-card';button.dataset.level=String(entry.number);
      button.disabled=entry.number>progress.unlocked;button.textContent=String(entry.number);
      if(entry.number===progress.currentLevel)button.classList.add('current');
      const small=document.createElement('small');small.textContent=progress.completedCampaign.includes(entry.number)?'已完成':button.disabled?'待解锁':'挑战';button.append(small);
      if(progress.completedCampaign.includes(entry.number))button.classList.add('completed');
      button.addEventListener('click',()=>{unlockAudio();loadLevel('campaign',index);});grid.append(button);
    });
  }
  function renderChallenges() {
    const pageSize=24,count=catalog.challenges.length,pages=Math.ceil(count/pageSize);
    challengePage=clamp(challengePage,0,Math.max(0,pages-1));
    const grid=$('challenge-grid');grid.replaceChildren();
    catalog.challenges.slice(challengePage*pageSize,(challengePage+1)*pageSize).forEach((entry,offset)=>{
      const index=challengePage*pageSize+offset,button=document.createElement('button');button.className='level-card';button.dataset.challengeIndex=String(index);button.textContent=`挑战 ${index+1}`;
      const dimensions=document.createElement('small');dimensions.textContent=`${entry.XSize} × ${entry.YSize} · ${entry.arrowCount} 根`;button.append(dimensions);
      if(progress.completedChallenges.includes(entry.id)){button.classList.add('completed');const done=document.createElement('small');done.textContent='已完成';button.append(done);}
      button.addEventListener('click',()=>{unlockAudio();loadLevel('challenge',index);});grid.append(button);
    });
    $('challenge-count').textContent=`${count} 张原地图 · H5重建排列`;$('challenge-page').textContent=`${challengePage+1} / ${pages}`;
    $('challenge-prev').disabled=challengePage<=0;$('challenge-next').disabled=challengePage>=pages-1;grid.scrollTop=0;
  }

  async function loadResources() {
    const names=['ArrowHead','ArrowEnd','Heart','HeartSlot','FingerHovering','FingerPressing','SettingsIcon','HomeIcon','RetryIcon','ChallangeIcon'];
    let loaded=0;const tick=()=>{$('loading-progress').style.width=`${++loaded/(names.length+1)*100}%`;};
    try {
      await Promise.all([fetch('./levels.json').then(response=>{if(!response.ok)throw Error(`目录加载失败 (${response.status})`);return response.json();}).then(data=>{
        if(!Array.isArray(data.levels)||data.levels.length!==40||!Array.isArray(data.challenges))throw Error('关卡目录不完整');catalog=data;tick();
      }),...names.map(name=>new Promise((resolve,reject)=>{
        const image=new Image();image.onload=()=>{images.set(name,image);tick();resolve();};image.onerror=()=>reject(Error(`图片加载失败：${name}`));image.src=`./assets/images/${name}.png`;
      }))]);
      ready=true;refreshHome();setScene(consentAccepted?'home':'consent');status('箭头棋盘准备完成。');
    }catch(error){console.error(error);$('loading-message').textContent=error.message;$('loading-retry').hidden=false;}
  }
  async function getMap(entry) {
    if(mapCache.has(entry.id))return mapCache.get(entry.id);
    if(!entry.path.startsWith('./assets/levels/'))throw Error('关卡路径异常');
    const response=await fetch(entry.path);if(!response.ok)throw Error(`关卡加载失败 (${response.status})`);
    const map=await response.json();
    if(!Number.isInteger(map.XSize)||!Number.isInteger(map.YSize)||!Array.isArray(map.Arrows)||!map.Arrows.length)throw Error('关卡内容异常');
    mapCache.set(entry.id,map);while(mapCache.size>3)mapCache.delete(mapCache.keys().next().value);return map;
  }
  async function loadLevel(mode,index) {
    if(mode==='challenge'&&!challengesUnlocked()){notify('请先完成主线第3关');return;}
    const pool=mode==='campaign'?catalog.levels:catalog.challenges;index=clamp(index,0,pool.length-1);const entry=pool[index];if(!entry)return;
    const generation=++loadGeneration;setScene('loading');$('loading-message').textContent=`正在准备${mode==='campaign'?'主线关卡':'扩展挑战'} ${index+1}…`;$('loading-retry').hidden=true;
    $('loading-progress').style.width='35%';loadRetry=()=>loadLevel(mode,index);pointers.clear();pinch=null;
    try {
      const map=await getMap(entry);if(generation!==loadGeneration)return;
      state=createLevelState(map,{level:entry.number||index+1,mode,index});currentEntry=entry;
      if(mode==='campaign')progress.currentLevel=state.level;else progress.lastChallenge=index;saveProgress();
      resetCamera();setScene('game');refreshGameUI();playSound('Tap');status(`${mode==='campaign'?'主线':'扩展挑战'}第${index+1}关，共${state.arrows.length}根箭头。`);
      // Only the selected map is required. No bulk download of thousands of maps.
    }catch(error){if(generation!==loadGeneration)return;console.error(error);$('loading-message').textContent=error.message;$('loading-retry').hidden=false;}
  }

  function resetCamera() {
    if(!state)return;
    camera={zoom:1,panX:0,panY:0,baseCell:Math.min(18,(BOARD.width-34)/Math.max(1,state.XSize-1),(BOARD.height-34)/Math.max(1,state.YSize-1)),centerX:180,centerY:BOARD.y+BOARD.height/2};cacheDirty=true;refreshZoom();
  }
  function worldToScreen(point) {
    const scale=camera.baseCell*camera.zoom;
    return {x:camera.centerX+camera.panX+(point.x-(state.XSize-1)/2)*scale,y:camera.centerY+camera.panY-(point.y-(state.YSize-1)/2)*scale};
  }
  function screenToWorld(point) {
    const scale=camera.baseCell*camera.zoom;
    return {x:(point.x-camera.centerX-camera.panX)/scale+(state.XSize-1)/2,y:-(point.y-camera.centerY-camera.panY)/scale+(state.YSize-1)/2};
  }
  function constrainPan() {
    if(!state)return;
    const scale=camera.baseCell*camera.zoom,maxX=(state.XSize-1)*scale/2+BOARD.width/2-24,maxY=(state.YSize-1)*scale/2+BOARD.height/2-24;
    camera.panX=clamp(camera.panX,-maxX,maxX);camera.panY=clamp(camera.panY,-maxY,maxY);
  }
  function refreshZoom(){$('zoom-label').textContent=`${Math.round(camera.zoom*100)}%`;}
  function zoomAround(factor,point={x:camera.centerX,y:camera.centerY}) {
    if(!state)return;
    const anchor=screenToWorld(point);camera.zoom=clamp(camera.zoom*factor,1,6);
    const scale=camera.baseCell*camera.zoom;
    camera.panX=point.x-camera.centerX-(anchor.x-(state.XSize-1)/2)*scale;camera.panY=point.y-camera.centerY+(anchor.y-(state.YSize-1)/2)*scale;
    constrainPan();cacheDirty=true;refreshZoom();
  }
  $('zoom-in').addEventListener('click',()=>zoomAround(1.35));$('zoom-out').addEventListener('click',()=>zoomAround(1/1.35));$('zoom-reset').addEventListener('click',resetCamera);
  const inBoard=p=>p.x>=BOARD.x&&p.x<=BOARD.x+BOARD.width&&p.y>=BOARD.y&&p.y<=BOARD.y+BOARD.height;
  function localPoint(event){const r=canvas.getBoundingClientRect();return {x:(event.clientX-r.left)*WIDTH/r.width,y:(event.clientY-r.top)*HEIGHT/r.height};}
  canvas.addEventListener('pointerdown',event=>{
    if(scene!=='game'||!state||state.failed||state.won||(event.pointerType==='mouse'&&event.button!==0))return;
    const point=localPoint(event);if(!inBoard(point))return;
    canvas.setPointerCapture(event.pointerId);pointers.set(event.pointerId,{...point,start:point,startTime:performance.now(),moved:false,panX:camera.panX,panY:camera.panY});
    if(pointers.size===2){const values=[...pointers.values()],center={x:(values[0].x+values[1].x)/2,y:(values[0].y+values[1].y)/2};
      pinch={distance:Math.hypot(values[1].x-values[0].x,values[1].y-values[0].y),zoom:camera.zoom,anchor:screenToWorld(center)};for(const p of pointers.values())p.moved=true;}
  });
  canvas.addEventListener('pointermove',event=>{
    const pointer=pointers.get(event.pointerId);if(!pointer)return;
    const point=localPoint(event);pointer.x=point.x;pointer.y=point.y;
    if(pointers.size>=2&&pinch){
      const values=[...pointers.values()],center={x:(values[0].x+values[1].x)/2,y:(values[0].y+values[1].y)/2};
      const distance=Math.hypot(values[1].x-values[0].x,values[1].y-values[0].y);camera.zoom=clamp(pinch.zoom*distance/Math.max(1,pinch.distance),1,6);
      const scale=camera.baseCell*camera.zoom;camera.panX=center.x-camera.centerX-(pinch.anchor.x-(state.XSize-1)/2)*scale;camera.panY=center.y-camera.centerY+(pinch.anchor.y-(state.YSize-1)/2)*scale;
      constrainPan();cacheDirty=true;refreshZoom();return;
    }
    const dx=point.x-pointer.start.x,dy=point.y-pointer.start.y;
    if(pointer.moved||Math.hypot(dx,dy)>6){pointer.moved=true;camera.panX=pointer.panX+dx;camera.panY=pointer.panY+dy;constrainPan();cacheDirty=true;}
  });
  function endPointer(event,cancel=false) {
    const pointer=pointers.get(event.pointerId);if(!pointer)return;
    const wasPinching=pointers.size>=2||!!pinch;pointers.delete(event.pointerId);
    if(wasPinching){for(const p of pointers.values()){p.moved=true;p.start={x:p.x,y:p.y};p.panX=camera.panX;p.panY=camera.panY;}pinch=null;}
    if(!cancel&&!pointer.moved&&!wasPinching&&performance.now()-pointer.startTime<650)clickAt(localPoint(event));
  }
  canvas.addEventListener('pointerup',event=>endPointer(event));canvas.addEventListener('pointercancel',event=>endPointer(event,true));
  canvas.addEventListener('contextmenu',event=>event.preventDefault());
  canvas.addEventListener('wheel',event=>{if(scene!=='game'||!state)return;const p=localPoint(event);if(!inBoard(p))return;event.preventDefault();zoomAround(Math.exp(-event.deltaY*.002),p);},{passive:false});

  function arrowBounds(arrow) {
    const points=arrow.points.map(worldToScreen),margin=Math.max(7,camera.baseCell*camera.zoom*.4);
    const xs=points.map(p=>p.x),ys=points.map(p=>p.y),minX=Math.min(...xs)-margin,minY=Math.min(...ys)-margin;
    return {x:minX,y:minY,width:Math.max(...xs)-minX+margin,height:Math.max(...ys)-minY+margin};
  }
  function arrowClickPoint(arrow) {
    const points=arrow.points.map(worldToScreen),visible=points.find(inBoard);return visible||points[0];
  }
  function findArrow(point) {
    let best=-1,distance=Infinity;
    for(const arrow of state.arrows){
      if(arrow.status==='moving'||arrow.status==='removed')continue;
      const points=arrow.points.map(worldToScreen);let d=Math.hypot(point.x-points[0].x,point.y-points[0].y);
      for(let i=1;i<points.length;i++)d=Math.min(d,segmentDistance(point,points[i-1],points[i]));
      if(d<distance){distance=d;best=arrow.id;}
    }
    return distance<=Math.max(7,camera.baseCell*camera.zoom*.37)?best:-1;
  }
  function clickAt(point) {
    if(scene!=='game'||!state||state.paused||state.failed||state.won||state.failAt||state.winAt||!inBoard(point))return;
    unlockAudio();const id=findArrow(point);if(id<0)return;const arrow=state.arrows[id];if(arrow.status!=='idle')return;
    state.moves++;state.hintId=-1;state.hintUntil=0;
    const blockers=forwardBlockers(state,id);arrow.blockedBy=blockers;
    if(blockers.length){
      state.lives=Math.max(0,state.lives-1);arrow.status='blocked';arrow.animationStart=gameTime;arrow.animationDuration=BLOCK_MS;playSound('Mistake',.7);
      if(state.lives===0)state.failAt=gameTime+BLOCK_MS;else notify('前方有箭头挡路，先移走它');
    }else{
      arrow.status='moving';arrow.animationStart=gameTime;
      const {x:dx,y:dy}=arrow.direction,{x,y}=arrow.head;
      const mapExit=dx>0?state.XSize-x:dx<0?x+1:dy>0?state.YSize-y:y+1;
      const headScreen=worldToScreen(arrow.head),scale=camera.baseCell*camera.zoom;
      const viewExit=dx>0?(BOARD.x+BOARD.width-headScreen.x)/scale:dx<0?(headScreen.x-BOARD.x)/scale:dy>0?(headScreen.y-BOARD.y)/scale:(BOARD.y+BOARD.height-headScreen.y)/scale;
      // Small tutorial grids occupy only the center of the white canvas. Keep
      // drawing until the tail leaves the visible viewport, not mid-screen.
      const exit=Math.max(mapExit,viewExit,0);
      arrow.exitDistance=arrow.pathLength+exit+1.4;
      arrow.animationDuration=clamp(arrow.exitDistance*22+260,700,1800);arrow.travel=0;playSound('Arrow',.68);
    }
    cacheDirty=true;refreshGameUI();
  }
  function updateAnimation() {
    let changed=false;
    for(const arrow of state.arrows){
      const age=gameTime-arrow.animationStart;
      if(arrow.status==='blocked'&&age>=BLOCK_MS){arrow.status='idle';changed=true;}
      if(arrow.status==='moving'){
        const t=clamp(age/arrow.animationDuration,0,1),ease=t*t*(3-2*t);arrow.travel=arrow.exitDistance*ease;
        if(t>=1){arrow.status='removed';state.removed++;changed=true;}
      }
    }
    if(state.hintUntil&&gameTime>=state.hintUntil){state.hintUntil=0;state.hintId=-1;changed=true;}
    if(changed){cacheDirty=true;refreshGameUI();}
    if(state.failAt&&gameTime>=state.failAt){state.failAt=0;state.failed=true;setScene('failed');playSound('LevelFail',.7);status('三颗心已用完，可以免费重新挑战。');}
    if(!state.failed&&state.removed===state.arrows.length&&!state.winAt&&!state.won)state.winAt=gameTime+WIN_DELAY;
    if(state.winAt&&gameTime>=state.winAt){state.winAt=0;state.won=true;completeLevel();}
  }
  function completeLevel() {
    if(state.mode==='campaign'){
      if(!progress.completedCampaign.includes(state.level))progress.completedCampaign.push(state.level);
      progress.unlocked=Math.max(progress.unlocked,Math.min(catalog.levels.length,state.level+1));
      progress.currentLevel=Math.min(catalog.levels.length,state.level+1);
    }else if(!progress.completedChallenges.includes(currentEntry.id))progress.completedChallenges.push(currentEntry.id);
    saveProgress();$('win-detail').textContent=`${state.mode==='campaign'?'主线关卡':'扩展挑战'} ${state.index+1} · 点击 ${state.moves} 次 · 剩余 ${state.lives} 颗心`;
    $('win-screen').querySelector('.win-stars').textContent=state.lives>=3?'✦ ✦ ✦':state.lives===2?'✦ ✦':'✦';
    const pool=state.mode==='campaign'?catalog.levels:catalog.challenges;
    $('next-button').textContent=state.index+1<pool.length?'下一关':state.mode==='campaign'?'返回主线关卡':'返回扩展图库';
    setScene('won');playSound('Complete',.75);status('棋盘已清空，关卡完成。');
  }
  function refreshGameUI() {
    if(!state)return;
    $('mode-label').textContent=state.mode==='campaign'?'主线关卡':'扩展挑战';$('level-label').textContent=`第 ${state.index+1} 关`;
    $('arrows-label').textContent=`剩余 ${state.arrows.length-state.removed} / ${state.arrows.length} 根`;$('moves-label').textContent=`点击 ${state.moves} 次`;
    [...$('heart-bar').children].forEach((heart,i)=>heart.classList.toggle('lost',i>=state.lives));$('heart-bar').setAttribute('aria-label',`剩余${state.lives}颗心`);
    $('tutorial-message').hidden=!(state.mode==='campaign'&&state.level===1&&state.moves===0);refreshZoom();
  }
  $('hint-button').addEventListener('click',()=>{
    if(scene!=='game'||!state||state.failAt||state.winAt)return;unlockAudio();
    const arrow=state.arrows.find(a=>a.status==='idle'&&!forwardBlockers(state,a.id).length);
    if(!arrow){notify('等待移动完成后再试');return;}
    state.hintId=arrow.id;state.hintUntil=gameTime+2200;cacheDirty=true;playSound('Tap');
    const point=worldToScreen(arrow.head);
    if(!inBoard(point)){camera.panX-=(point.x-camera.centerX);camera.panY-=(point.y-camera.centerY);constrainPan();cacheDirty=true;}
    notify('高亮的箭头现在可以离场');
  });
  function restart(){if(state){unlockAudio();loadLevel(state.mode,state.index);}}
  $('restart-button').addEventListener('click',restart);$('pause-restart').addEventListener('click',restart);$('retry-button').addEventListener('click',restart);
  $('pause-button').addEventListener('click',()=>{if(scene==='game'&&state){state.paused=true;pointers.clear();pinch=null;setScene('paused');}});
  $('resume-button').addEventListener('click',()=>{if(state){state.paused=false;setScene('game');unlockAudio();}});
  $('home-button').addEventListener('click',goHome);$('win-home').addEventListener('click',goHome);$('fail-home').addEventListener('click',goHome);
  $('next-button').addEventListener('click',()=>{
    if(!state||!state.won)return;unlockAudio();playSound('LevelIncrease');
    const pool=state.mode==='campaign'?catalog.levels:catalog.challenges;
    if(state.index+1<pool.length)loadLevel(state.mode,state.index+1);
    else if(state.mode==='campaign'){renderCampaign();setScene('campaign');}else{renderChallenges();setScene('challenge');}
  });

  function resize() {
    const r=canvas.getBoundingClientRect(),dpr=Math.min(2,devicePixelRatio||1);canvas.width=Math.round(r.width*dpr);canvas.height=Math.round(r.height*dpr);cacheDirty=true;
  }
  addEventListener('resize',resize);resize();
  document.addEventListener('visibilitychange',()=>{lastFrame=performance.now();pointers.clear();pinch=null;syncMusic();});
  function tint(name,color) {
    const id=`${name}:${color}`;if(tints.has(id))return tints.get(id);
    const image=images.get(name);if(!image)return null;
    const off=document.createElement('canvas');off.width=image.width;off.height=image.height;const c=off.getContext('2d');c.drawImage(image,0,0);c.globalCompositeOperation='source-in';c.fillStyle=color;c.fillRect(0,0,off.width,off.height);tints.set(id,off);return off;
  }
  function roundBox(x,y,w,h,r,color) {
    ctx.beginPath();ctx.moveTo(x+r,y);ctx.arcTo(x+w,y,x+w,y+h,r);ctx.arcTo(x+w,y+h,x,y+h,r);ctx.arcTo(x,y+h,x,y,r);ctx.arcTo(x,y,x+w,y,r);ctx.closePath();ctx.fillStyle=color;ctx.fill();
  }
  function paintArrow(arrow,points=arrow.points,color='#17203e',shake=0,alpha=1) {
    const scale=camera.baseCell*camera.zoom,screen=points.map(worldToScreen);if(!screen.length)return;
    ctx.save();ctx.globalAlpha=alpha;ctx.translate(shake,0);ctx.strokeStyle=color;ctx.lineWidth=Math.max(1.55,scale*.16);ctx.lineCap='round';ctx.lineJoin='round';
    ctx.beginPath();ctx.moveTo(screen[0].x,screen[0].y);for(let i=1;i<screen.length;i++)ctx.lineTo(screen[i].x,screen[i].y);ctx.stroke();
    const head=tint('ArrowHead',color),size=Math.max(6,scale*.65),angle=Math.atan2(-arrow.direction.y,arrow.direction.x)+Math.PI/2;
    ctx.save();ctx.translate(screen[0].x,screen[0].y);ctx.rotate(angle);
    if(head)ctx.drawImage(head,-size*.46,-size*.75,size*.92,size);
    else{ctx.fillStyle=color;ctx.beginPath();ctx.moveTo(0,-size*.75);ctx.lineTo(size*.46,size*.25);ctx.lineTo(-size*.46,size*.25);ctx.closePath();ctx.fill();}ctx.restore();
    const tail=screen.at(-1);ctx.beginPath();ctx.arc(tail.x,tail.y,Math.max(.9,scale*.08),0,Math.PI*2);ctx.fillStyle=color;ctx.fill();ctx.restore();
  }
  function isDynamic(arrow){return arrow.status==='moving'||arrow.status==='blocked'||arrow.id===state.hintId;}
  function rebuildCache() {
    cache.width=canvas.width;cache.height=canvas.height;ctx=cache.getContext('2d');ctx.setTransform(canvas.width/WIDTH,0,0,canvas.height/HEIGHT,0,0);
    ctx.save();ctx.beginPath();ctx.rect(BOARD.x,BOARD.y,BOARD.width,BOARD.height);ctx.clip();
    if(gridEnabled){
      ctx.fillStyle='#d4d8fc';const scale=camera.baseCell*camera.zoom;
      for(let y=0;y<state.YSize;y++)for(let x=0;x<state.XSize;x++){
        const p=worldToScreen({x,y});if(!inBoard(p))continue;ctx.beginPath();ctx.arc(p.x,p.y,Math.max(.6,Math.min(1.55,scale*.055)),0,Math.PI*2);ctx.fill();
      }
    }
    for(const arrow of state.arrows)if(arrow.status!=='removed'&&!isDynamic(arrow))paintArrow(arrow);
    ctx.restore();ctx=mainCtx;cacheDirty=false;
  }
  function drawBoard() {
    if(cacheDirty||cache.width!==canvas.width||cache.height!==canvas.height)rebuildCache();ctx.drawImage(cache,0,0,WIDTH,HEIGHT);
    ctx.save();ctx.beginPath();ctx.rect(BOARD.x,BOARD.y,BOARD.width,BOARD.height);ctx.clip();
    for(const arrow of state.arrows){
      if(arrow.status==='moving'){
        const progress=clamp((gameTime-arrow.animationStart)/arrow.animationDuration,0,1);paintArrow(arrow,movingPath(arrow,arrow.travel),'#505db7',0,1-clamp((progress-.9)*8,0,.65));
      }else if(arrow.status==='blocked')paintArrow(arrow,arrow.points,'#ff536d',Math.sin((gameTime-arrow.animationStart)*.055)*3.5);
      else if(arrow.id===state.hintId&&arrow.status==='idle'){
        const head=worldToScreen(arrow.head),radius=10+Math.sin(gameTime*.007)*2;
        ctx.beginPath();ctx.arc(head.x,head.y,radius,0,Math.PI*2);ctx.fillStyle='#7e87ff25';ctx.fill();paintArrow(arrow,arrow.points,'#6470ff');
      }
    }
    if(state.mode==='campaign'&&state.level===1&&state.moves===0){
      const target=state.arrows[0],head=worldToScreen(target.head),tail=worldToScreen(target.points.at(-1)),image=images.get('FingerHovering');
      if(image){const width=43,height=width*image.height/image.width,bob=Math.sin(gameTime*.006)*3;ctx.save();ctx.shadowColor='#17203e33';ctx.shadowBlur=3;ctx.drawImage(image,head.x-5,(head.y+tail.y)/2-8+bob,width,height);ctx.restore();}
    }
    ctx.restore();
  }
  function draw() {
    ctx=mainCtx;ctx.setTransform(canvas.width/WIDTH,0,0,canvas.height/HEIGHT,0,0);ctx.fillStyle='white';ctx.fillRect(0,0,WIDTH,HEIGHT);
    if(state)drawBoard();
  }
  function frame(now) {
    const delta=Math.max(0,Math.min(120,now-lastFrame));lastFrame=now;
    if(state&&scene==='game'&&!state.paused&&!document.hidden){gameTime+=delta;updateAnimation();}
    if(!$('toast').hidden&&now>toastUntil)$('toast').hidden=true;
    draw();requestAnimationFrame(frame);
  }
  function deepFreeze(value){if(value&&typeof value==='object'){Object.values(value).forEach(deepFreeze);Object.freeze(value);}return value;}
  function snapshot() {
    const s=state;
    return deepFreeze({ready,scene,width:WIDTH,height:HEIGHT,board:{...BOARD},level:s?.level||progress.currentLevel,mode:s?.mode||'campaign',index:s?.index||0,levelCount:catalog.levels.length,challengeCount:catalog.challenges.length,challengeUnlocked:challengesUnlocked(),challengePage,unlockedLevel:progress.unlocked,completedCampaign:progress.completedCampaign.slice(),consentAccepted,music:musicEnabled,musicEnabled,sfxEnabled,gridEnabled,lives:s?.lives??3,moves:s?.moves||0,remaining:s?s.arrows.length-s.removed:0,totalArrows:s?.arrows.length||0,removed:s?.removed||0,paused:s?.paused||false,won:s?.won||false,failed:s?.failed||false,busy:!!s&&(s.arrows.some(a=>a.status==='moving'||a.status==='blocked')||!!s.winAt||!!s.failAt),winAt:s?.winAt||0,failAt:s?.failAt||0,hintId:s?.hintId??-1,hintUntil:s?.hintUntil||0,gameTime,camera:{...camera},map:s?{XSize:s.XSize,YSize:s.YSize,id:currentEntry.id,name:currentEntry.name}:null,arrows:s?.arrows.map(a=>({id:a.id,indices:a.indices.slice(),points:a.points.map(p=>({...p})),head:{...a.head},direction:{...a.direction},status:a.status,pathLength:a.pathLength,travel:a.travel,animationStart:a.animationStart,animationDuration:a.animationDuration,blockedBy:a.blockedBy.slice(),screenPoints:a.points.map(worldToScreen),clickPoint:arrowClickPoint(a),bounds:arrowBounds(a),movingPoints:a.status==='moving'?movingPath(a,a.travel):[]}))||[],audio:{musicEnabled,sfxEnabled,audioEnabled,bgmPaused:bgm.paused,bgmCurrentTime:bgm.currentTime,bgmMuted:bgm.muted,audioContextState:audioContext?.state||'uninitialized',sfxDecodedCount:buffers.size,sfxPlayed},entryPath:currentEntry?.path||null});
  }
  Object.defineProperty(window,'ArrowH5',{value:Object.freeze({snapshot}),writable:false,configurable:false});
  refreshSettings();requestAnimationFrame(frame);loadResources();
}
