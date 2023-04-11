
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
}
RunIO(Eval([["$","val",["$","p",["$","i",["p","val"]]]],["$","+",["$","0","0"]]],{}))

