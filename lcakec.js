let {reduceUsing} = require('shift-reducer')

const cyrb53 = (str, seed = 0) => {
    let h1 = 0xdeadbeef ^ seed, h2 = 0x41c6ce57 ^ seed;
    for(let i = 0, ch; i < str.length; i++) {
        ch = str.charCodeAt(i);
        h1 = Math.imul(h1 ^ ch, 2654435761);
        h2 = Math.imul(h2 ^ ch, 1597334677);
    }
    h1  = Math.imul(h1 ^ (h1 >>> 16), 2246822507);
    h1 ^= Math.imul(h2 ^ (h2 >>> 13), 3266489909);
    h2  = Math.imul(h2 ^ (h2 >>> 16), 2246822507);
    h2 ^= Math.imul(h1 ^ (h1 >>> 13), 3266489909);
  
    return 4294967296 * (2097151 & h2) + (h1 >>> 0);
};

let srcBase = `
// Credit to http://m1el.github.io/smallest-lambda-eval/
function Eval(prog, env) {
    if (typeof prog === 'string') {
        // lookup a variable
        return env[prog];
    } else if (prog[0] === '$') {
        // constructing a new lambda
        return (arg) => Eval(prog[2], { ...env, [prog[1]]: arg });
    } else {
        // function application
        return Eval(prog[0], env)(Eval(prog[1], env));
    }
}
function FromChurch(f) {
    var i = 0;
    f(function (x) {
        i++;
        return x;
    })(function (x) {
        return x;
    })(undefined);
}
function ToChurch(i) {
    return function (a) {
        return function (b) {
            var c = b;
            for (let j = 0; j < i; j++)c = a(c);
            return c
        }
    }
}
function FromArray(x) {
    return x([])((a) => (v) => [...a, v])
}
function ToArray(x) {
    return function (n) {
        return function (s) {
            var o = n;
            for (var i of x) {
                o = s(o)(i);
            }
            return o
        }
    }
}
function FromString(x) {
    return String.fromCodePoint(...FromArray(x).map(FromChurch))
}
function ToString(s){
    return toArray([...s].map(x => x.codePointAt(0)).map(FromChurch))
}
var opcodes = {
    0: 'io_ref_new',
    1: 'io_ref_read',
    2: 'io_ref_write',
}
function RunIO(prog) {
    return prog(function(x){
        return x;
    })(function (ty) {
        return function (pay) {
            return function (cont) {
                var then = function(x){
                    return RunIO(cont(x))
                }
                switch (opcodes[FromChurch(ty)]) {
                    case 'io_ref_new':
                        var x = Math.random().toString();
                        RunIO["io_ref/" + x] = pay;
                        return then(ToString(x));
                    case 'io_ref_read':
                        return then(RunIO["io_ref/" + FromString(pay)])
                    case 'io_ref_write':
                        return pay(function(a){
                            return function(b){
                                RunIO["io_ref/" + FromString(a)] = b;
                                return then(b);
                            }
                        })
                }
            }
        }
    })
}`

function vari(x){
    return x;
}

function abs(a,b){
    return ['$',a,b]
}

function app(a,b){
    return [a,b]
}

function appx(...a){
    var b = a[0];
    for(var i in a){
        if(i != 0){
            b = app(b,a[i])
        }
    }
    return b
}

function subst(x,b,c){
    if(typeof x == 'string'){
        if(x === b)return c;
        return x;
    }else if (x[0] == '$'){
        if(x[1] == b){
            return x;
        }
        return abs(x[1],subst(x[2],b,c));
    }
    return app(subst(x[0],b,c),subst(x[1],b,c))
}

Function.prototype.fuse = function(){
    var a = abs('$$0',this('$$0'))
    var h = cyrb53(JSON.stringify(a))
    return abs(`h${h}`,subst(a[2],'$$0',`h${h}`))
}

function createChurch(n){
    var v = '0';
    for(let i = 0; i < n; i++){
        v = ['+',v];
    }
    return ['$','+',['$','0',v]]
}
function createList(n){
    var v = 'null';
    for(var i of n){
        v = app('push')(v)(i);
    }
    return abs('null',abs('push',v))
}
function createString(s){
    return createList([...s].map(x => x.codePointAt(0)).map(createChurch))
}
function createBool(b){
    return abs('x',app('y',b ? 'x' : 'y'))
}
var yb = abs('f',abs('x',app('x',abs('z',app(app(app('f','f'),'x'),'z')))))
var y = app(yb,yb)
var IO = {
    pure: abs('val',abs('p',abs('i',app('p','val')))),
    bind: app(y,abs('bind',abs('m',abs('f',app(app('m','f'),abs('ty',abs('pay',abs('cont',abs('h',app(app(app('h','ty'),'pay'),abs('x',app(app('bind',app('cont','x')),'f')))))))))))),
    name: 'io'
}
var createIO = abs('t',abs('p',abs('pu',abs('i',appx('i','t','p',IO.pure)))))
var newIORef = appx(createIO,createChurch(0))
var readIORef = appx(createIO,createChurch(1))
var writeIORef = abs('r',abs('v',appx(createIO,createChurch(2),abs('f',appx('f','r','v')))))

function warp(x,{pure,bind,name} = IO){
    if(typeof x == 'string'){
        return app(pure,name + '$' + x);
    }else if (x[0] == '$'){
        return app(pure,abs(name + '$' + x[1],warpIO(x[2])))
    }else if(x[0] == 'splice_' + name){
        return x[1];
    }
    return appx(bind,warp(x[0],{pure,bind,name}),abs('f',appx(bind,warp(x[1],{pure,bind,name}),abs('x',app('f','x')))))
}

function don(m,...a){
    if(a.length == 1){
        return a[0]
    }
    var b = a.shift();
    var c = a.shift();
    return appx(m.bind,c,abs(b,don(m,...a)))
}


var pred = abs('n',abs('f',abs('x',app(app(app('n',abs('g',abs('h',app('h',app('g','f'))))),abs('u','x')),abs('u','u')))))
var isZero = abs('n',app(app('n',abs('x',createBool(false)),createBool(true))))
var l_and = abs('p',abs('q',app(app('p','q'),'p')))
var minus = abs('a',abs('b',app(app('b',pred),'a')))
var leq = abs('m',abs('n',app(isZero,app(app(minus,'m'),'n'))))
var eq = abs('m',abs('n',app(app(l_and,app(app(leq,'m'),'n')),app(app(leq,'n'),'m'))))

var tru = abs('t',abs('f','t'))
var fals = abs('t',abs('f','f'))

var jsFunBase = abs('x',abs('fn',abs('truthy',abs('falsy',app('fn','x')))))
var jsTruthy = abs('t',abs('v',abs('fn',abs('truthy',abs('falsy',app(app('truthy','t'),'v'))))))
var jsFalsy = abs('t',app('fn',abs('truthy',abs('falsy',app('falsy','t')))))

var sempty = abs('e',abs('c','e'))
var scons = abs('h',abs('t',abs('e',abs('c',appx('c','h','t')))))

var stoc = appx(y,function(a){
    return abs('l',abs('n',abs('c',appx('l','n',abs('a',abs('b',appx('c','a',appx(a,'b','n','c'))))))))
}.fuse)

var ctos = abs('a',appx('a',sempty,scons))

var strEq = appx(y,abs('strEq',abs('a',abs('b',appx('a',appx('b',tru,abs('_a',abs('_b',fals))),abs('c',abs('d',appx('b',fals,abs('e',abs('f',appx(eq,'c','e',appx('strEq','d','f'),fals)))))))))))

var churchSucc = abs('x',abs('o',abs('s',app('s',appx('x','o','s')))))

var TY_NULL = 0;

var jsNull = app(jsFalsy,createChurch(TY_NULL))

var getVarS = getGetVarSlot => abs('v',abs('p',abs('b',abs('l',appx(stoc,'l',abs('_',appx(free.pure,jsNull)),abs('f',abs('p',appx(getGetVarSlot('f'),'p'))),'v')))))

var free = {
    name: 'free',
    pure: abs('x',abs('p',abs('b',abs('l',app('p','x'))))),
    bind: abs('m',abs('f',abs('p',abs('b',abs('l',appx('b',appx('m','p','b','l'),abs('v',appx('f','v','p','b','l'))))))))
}

var addVarS = push => abs('f',abs('v',abs('p',abs('b',abs('l',appx('f',
    abs('v',abs('x',app('p','v'))), // pure
    abs('m',abs('f',abs('x',appx('b',app('m','x'),abs('v',appx('f','v','x')))))), // bind
    appx(scons,push(
        abs('m',abs('x','m')), //lift
        abs('r',abs('v',abs('x',appx(isZero,'v',app(free.pure,'x'),abs('_', appx('r',appx(pred,'v'))))))), //getVar
        abs('f',abs('r',appx(f,abs('v',app('v','r'))))) //weave
    ),'l'),
    'v'
))))))

var liftIOS = getLift => abs('i',abs('p',abs('b',app('l',appx(stoc,'l','i',abs('d',abs('m',app(getLift('d'),'m'))))))))

var composeWeaves = abs('a',abs('b',abs('f',app('a',abs('la',app('b',abs('lb',app('f',abs('m',app('la',app('lb','m')))))))))))

var weaveIO = getGetWeaveSlot => abs('f',abs('p',abs('b',abs('l',appx(stoc,'l',abs('a',abs('b',apx(composeWeaves,getGetWeaveSlot('a'),'b'))),abs('l',app('f',abs('m',app('l',appx('m','p','b','l'))))))))))


var readerT = old => ({
    base: old,
    lift: abs('x',abs('v','x')),
    pure: abs('x',abs('v',app(old.pure,'x'))),
    bind: abs('m',abs('f',abs('v',appx(old.bind,app('m','v'),abs('w',appx('f','w','v')))))),
    name: `readerT(${old.name})`
})

var contT = old => ({
    base: old,
    lift: abs('x',abs('cc',appx(old.bind,'x','cc'))),
    pure: abs('x',abs('cc',app('cc','x'))),
    bind: abs('m',abs('f',abs('cc',app('m',abs('x',appx('f','x','cc')))))),
    name: `contT(${old.name})`
})

var js = contT(readerT(free))

var getVarB = getGetVarSlot => abs('j',app(js.lift,abs('vs',appx(getVarS(getGetVarSlot),appx('vs','j')))))

var liftIOB = getLift => abs('i',app(js.lift,abs('v',appx(liftIOS(getLift),'i'))))

var pushBase = (a,b,c) => abs('f',appx('f',a,b,c))

var addVarB = push => abs('m',abs('v',abs('f',addVarS(push),appx('f',abs('n',appx(strEq,'m','n',createChurch(0),app(churchSucc,app('f','n'))))),'v')));

var weaveIOB = base => abs('f',app(js.lift,abs('v',app(weaveIO(base),abs('l',app('f',abs('m',app('l',appx('m',js.base.pure,'v')))))))))

var addVar = addVarB(pushBase)

js.addVar = addVar

var getGetVarSlotBase = x => app(x,abs('a',abs('b',abs('c','b'))))

var getLiftBase = x => app(x,abs('a',abs('b',abs('c','a'))))

var weaveBase = x => app(x,abs('a',abs('b',abs('c','c'))))

var jsWeave = weaveIOB(weaveBase)

js.weave = jsWeave

var getVar = getVarB(getGetVarSlotBase)

js.getVar = getVar

var liftIOJ = liftIOB(getLiftBase)

js.liftIO = liftIOJ

var jsFun = abs('f',app(js.weave,abs('l',app(IO.pure,app(jsFunBase,abs('args',app(js.liftIO,app('l',app('f','args')))))))))


console.log(srcBase + `
RunIO(Eval(${JSON.stringify(app(IO.pure,createChurch(0)))},{}))
`)