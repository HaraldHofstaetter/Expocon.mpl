Expocon := module()

option package;
export Generator, Word, grade, hom, wcoeff, 
       lyndon_words, lyndon_basis,
       rhs_legendre;
global `type/Generator`, `type/Word`, `print/Word`, `print/hom`;
local grade_gen, grade_word, lyndon_transform, genLW,
      lyndon_bracket, genLB;

`type/Generator` := proc (g) 
    #type(g, name) and grade(g) <> undefined     
    type(g, name) and type(g, noncommutative)
end proc;

`type/Word` := proc (w) 
    local i; 
    op(0, w) = Word and `and`(seq(type(op(i, w), Generator), i = 1 .. nops(w))) 
end proc;

`print/Word` := proc () 
    local i; 
    mul(args[i], i = 1 .. nargs) 
end proc;

grade_gen := proc (g::Generator) 
    if type(g, indexed) then
        return op(g)
    else
        return 1
    end
end proc;

grade_word := proc (w::Word) 
    local i; 
    option overload; 
    add(grade_gen(op(i, w)), i = 1 .. nops(w)) 
end proc;

grade := overload([grade_gen, grade_word]);

hom := proc (w::Word, ex::anything) 
    local i; 
    if type(ex, Generator) then 
        return LinearAlgebra[Transpose](LinearAlgebra[BandMatrix]([[seq(subs([false = 0, true = 1], 
            evalb(op(i, w) = ex)), i = 1 .. nops(w))]], 1, nops(w)+1, nops(w)+1)) 
    elif type(ex, `+`) then 
        return evalm(add(hom(w, op(i, ex)), i = 1 .. nops(ex))) 
    elif type(ex, `*`) then 
        return evalm(`&*`(seq(hom(w, op(i, ex)), i = 1 .. nops(ex)))) 
    elif type(ex, `^`) then 
        return evalm(hom(w, op(1, ex))^op(2, ex)) 
    elif type(ex, function) and op(0, ex) = Physics[Commutator] then 
        return evalm(`&*`(hom(w, op(1, ex)), hom(w, op(2, ex)))-`&*`(hom(w, op(2, ex)), hom(w, op(1, ex)))) 
    elif type(ex, function) and op(0, ex) = exp then 
        return LinearAlgebra[MatrixExponential](hom(w, op(ex))) 
    end if; 
    return ex*LinearAlgebra[IdentityMatrix](nops(w)+1) 
end proc;

`print/hom` := proc (w, ex) 
    varphi[w](ex) 
end proc;

wcoeff := proc (w::Word, ex::anything) 
    local H; 
    H := Matrix(hom(w, ex)); 
    H[1, LinearAlgebra[Dimension](H)[2]] 
end proc;

########################################
#Algorithm 2.1 from
#  K. Cattell, F. Ruskey, J. Sawada, M. Serra, C.R. Miers, Fast algorithms to generate necklaces, 
#  unlabeled necklaces and irreducible polynomials over GF(2), J. Algorithms 37 (2) (2000) 267–282

lyndon_transform := proc (w::(list(integer))) 
    local w1, c, x; 
    w1 := []; 
    c := 0; 
    for x in w[2 .. -1] do 
        if x = 1 then 
            c := c+1 
        else 
            w1 := [op(w1), c]; 
            c := 0 
        end if 
    end do; 
    w1 := [op(w1), c]; 
    w1 
end proc;

genLW := proc(k::integer, n::integer, t::integer, p::integer, trafo::boolean)
    global __a, __W;
    local j;
    if t>n then
        if p=n then
            if trafo then
                __W := [op(__W), lyndon_transform(__a[2..n+1])]
            else
                __W := [op(__W), __a[2..n+1]]
            end if
        end if
    else
        __a[t+1] := __a[t-p+1];
        genLW(k, n, t+1, p,  trafo);
        for j from __a[t-p+1]+1 to k-1 do
            __a[t+1] := j;
            genLW(k, n, t+1, t,  trafo)
        end do
    end if
end proc;

lyndon_words := proc(k::integer, n::integer)
    local trafo;
    global __a, __W;

    __a := [0$n+1];
    __W := [];
    trafo := k<2;
    genLW( `if`(trafo, 2, k), n, 1, 1, trafo);
    __W
end proc;


########################################
#Algorithm from
#  J. Sawada, F. Ruskey, Generating Lyndon brackets. An addendum to: Fast algorithms 
#  to generate necklaces, unlabeled necklaces and irreducible polynomials over GF(2),
#  J. Algorithms 46 (2003) 21–26

lyndon_bracket := proc(l::integer, r::integer, trafo::boolean)
    global __a, __split:
    if trafo and __a[l+1]=0 and __a[l+2..r+1]=[1$r-l] then
        return r-l
    elif not trafo and l=r then
        return __a[l+1]
    else        
        return [lyndon_bracket(l,__split[l,r]-1, trafo),
            lyndon_bracket(__split[l,r], r, trafo)]
    end if
end proc;

genLB := proc (k::integer, n::integer, t::integer, trafo::boolean)
    global __p, __a, __split, __B;
    local q, i, j;
    if t>n then
        if n=__p[1] then
            __B := [op(__B), lyndon_bracket(1, n, trafo)]
        end if
    else
        q := __p;
        for j from __a[t-__p[1]+1] to k-1 do
            __a[t+1] := j;
            for i from 1 to t-1 do
                if __a[t+1]<__a[t-__p[i]+1] then
                    __p[i] := 0
                end if;
                if __a[t+1]>__a[t-__p[i]+1] then
                    __p[i] := t-i+1
                end if
            end do;
            for i from t-1 to 1 by -1 do
                if __p[i+1]=t-i then
                    __split[i,t] := i+1
                else
                    __split[i,t] := __split[i+1,t]
                end if
            end do;
            genLB(k, n, t+1, trafo);
            __p := q
        end do
    end if
end proc;

lyndon_basis := proc(k::integer, n::integer)
    local trafo;
    global __a, __p, __split, __B;

    __a := [0$n+1];
    __p := [1$n];
    __split := array(1 .. n, 1 .. n, [[0$n]$n]);
    __B := [];
    trafo := k<2;
    genLB( `if`(trafo, 2, k), n, 1, trafo);
    __B
end proc;



########################################
rhs_legendre := proc(W::list(Word))
    local W1, p, w, L, l, s, c, k, T, v;
    W1 := [seq(map(grade, [op(w)]), w in W)];
    p := max(seq(add(w), w in W1));
    L := array([seq([seq((-1)^(m+n)*binomial(n, m)*binomial(m+n, m), n = 0 .. p-1)], m = 0 .. p-1)]);
    c := [];
    for w in W1 do 
        l := nops(w); 
        s := 0; 
        T := combinat[cartprod]([seq([`$`(1 .. k)], k in w)]); 
        while `not`(T[finished]) do v := T[nextvalue](); 
            s := s+mul(L[v[j], w[j]]*(1/add(v[j .. l])), j = 1 .. l) 
        end do; 
        c := [op(c), s] 
    end do;
    c
end proc;

end module;
