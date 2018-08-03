Expocon := module()

option package;

export Generator, Word, SimpleComuutator, grade, hom, homv, wcoeff, 
       lyndon_words, lyndon_coeffs, lyndon_basis, rightnormed_basis,
       lyndon_transformation_matrix,
       rhs_legendre;

global `type/Generator`, `type/Word`, 
       `type/SimpleCommutator`, `print/SimpleCommutator`;

local lyndon_transform, genLW,
      lyndon_bracket, genLB, convert_commutator,
      lexless, sort_lexorder, invperm, reverse, analyze_lyndon_word,
      lyndon2rightnormed, rightnormed_word2commutator;

`type/Generator` := proc (g) 
    type(g, name) and type(g, noncommutative)
end proc;

`type/Word` := list(Generator);

`type/SimpleCommutator` := proc (c) 
    op(0, c) = SimpleCommutator and nops(c) = 2 
end proc;

`print/SimpleCommutator` := proc () 
    [args[1], args[2]] 
end proc;

grade := proc(x::{Generator, Word})
    local i;
    if type(x, Generator) then
        if type(x, indexed) then
            return op(x)
        else
            return 1
        end
    else
       return add(grade(op(i, x)), i = 1 .. nops(x))
    end if
end proc;

hom := proc (w::Word, ex::anything) 
    local i; 
    if type(ex,name) and type(ex, noncommutative) then 
        return LinearAlgebra[Transpose](LinearAlgebra[BandMatrix]([[seq(subs([false = 0, true = 1], 
            evalb(op(i, w) = ex)), i = 1 .. nops(w))]], 1, nops(w)+1, nops(w)+1)) 
    elif type(ex, `+`) then 
        return evalm(add(hom(w, op(i, ex)), i = 1 .. nops(ex))) 
    elif type(ex, `*`) then 
        return evalm(`&*`(seq(hom(w, op(i, ex)), i = 1 .. nops(ex)))) 
    elif type(ex, `^`) then 
        return evalm(hom(w, op(1, ex))^op(2, ex)) 
    elif type(ex, SimpleCommutator) or (type(ex, function) and op(0, ex) = Physics[Commutator]) then 
        return evalm(`&*`(hom(w, op(1, ex)), hom(w, op(2, ex)))-`&*`(hom(w, op(2, ex)), hom(w, op(1, ex)))) 
    elif type(ex, function) and op(0, ex) = exp then 
        return LinearAlgebra[MatrixExponential](hom(w, op(ex))) 
    end if; 
    return ex*LinearAlgebra[IdentityMatrix](nops(w)+1) 
end proc;


homv := proc (w, ex, v) # no type checks here due to performance reasons
    local i, v1, v2, f, zero;
    if type(ex,name) and type(ex, noncommutative) then 
        return [seq(`if`(op(i, w)=ex, v[i+1], 0), i=1..nops(w)), 0]
    elif type(ex, `+`) then 
        return add(homv(w, op(i, ex), v), i=1..nops(ex))
    elif type(ex, `*`) then
        v1 := v;
        zero = [0$nops(w)+1];
        for i from nops(ex) to 1 by -1 do
            v1 := homv(w, op(i, ex), v1);           
            if v1=zero then
                return zero 
            end;
        end do;     
        return v1
    elif type(ex, anything^integer) then
        v1 := v;
        zero = [0$nops(w)+1];
        for i from 1 to op(2, ex) do
            v1 := homv(w, op(1, ex), v1);            
            if v1=zero then
                return zero 
            end;
        end do;     
        return v1
    elif type(ex, SimpleCommutator) or (type(ex, function) and op(0, ex) = Physics[Commutator]) then 
        return homv(w, op(1, ex), homv(w, op(2, ex), v)) - homv(w, op(2, ex), homv(w, op(1, ex), v)) 
    elif type(ex, exp(anything)) then 
        v1 := v;
        v2 := v;
        zero = [0$nops(w)+1];
        f := 1;
        for i from 1 to nops(w) do
            f := f*i;
            v1 := homv(w, op(ex), v1);
            if v1=zero then
                return v2;
            end;
            v2 := v2 + v1/f;
        end do;
        return v2
    end if; 
    return [seq(ex*x, x=v)]
end proc;

wcoeff := proc (w::Word, ex::anything) 
    homv(w, ex, [`$`(0, nops(w)), 1])[1]
end proc;


########################################
#Algorithm 2.1 from
#  K. Cattell, F. Ruskey, J. Sawada, M. Serra, C.R. Miers, Fast algorithms to generate necklaces, 
#  unlabeled necklaces and irreducible polynomials over GF(2), J. Algorithms 37 (2) (2000) 267–282

lyndon_transform := proc (w::(list(integer))) 
    local w1, c, x; 
    if w=[0] then 
        return NULL;
    end if;
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

genLW := proc(k::integer, n::integer, t::integer, p::integer, trafo::boolean, mg::{integer, infinity})
    global __a, __W;
    local j, w;
    if t>n then
        if p=n then
            if trafo then
                w := lyndon_transform(__a[2..n+1]);
                if max(w)<mg then
                    __W := [op(__W), w]
                end if;
            else
                __W := [op(__W), __a[2..n+1]]
            end if
        end if
    else
        __a[t+1] := __a[t-p+1];
        genLW(k, n, t+1, p,  trafo, mg);
        for j from __a[t-p+1]+1 to k-1 do
            __a[t+1] := j;
            genLW(k, n, t+1, t, trafo, mg)
        end do
    end if
end proc;

lyndon_words := proc(s::{integer, list(Generator), symbol}, q::{integer, list(integer)},
                     {max_generator_grade::{integer, infinity}:=infinity})
    local trafo, qq, n, k, w, x;
    global __a, __W;

    if type(s, list(Generator)) then
        k := nops(s)
    elif type(s, symbol) then
        k := 1
    else
        k := s
    end if;

    if type(q, integer) then
        qq := [q]
    else
        qq := q
    end if;

    trafo := k<2;
    __W := [];
    for n in qq do
        __a := [0$n+1];        
        genLW( `if`(trafo, 2, k), n, 1, 1, trafo, max_generator_grade)
    end do;

    if type(s, integer) then
       return __W
    else
        return [seq([seq(s[x+1], x=w)], w=__W)]
    end if
end proc;

lyndon_coeffs := proc(ex::anything, s::{list(Generator), symbol}, q::{integer, list(integer)},
                     {max_generator_grade::{integer, infinity}:=infinity,
                      exact::symbol:=`none`})
    global  __W;
    local k, qq, p, W, Wp, T, cc, j, w;

    if type(s, list(Generator)) then
        k := nops(s)
    else
        k := 1
    end;

    if type(q, integer) then
        qq := [q]
    else
        qq := q
    end if;

    qq := sort([op({op(qq)})]);
    p := qq[-1];
    if nops(qq)= 1 then
        Wp := lyndon_words(s, p, ':-max_generator_grade'=max_generator_grade);
        return [seq(homv(w, ex, [`$`(0, nops(w)), 1])[1], w=Wp)]
    end if;

    qq := qq[1..-2];
    W := lyndon_words(k, qq, ':-max_generator_grade'=max_generator_grade);
    Wp := lyndon_words(s, p, ':-max_generator_grade'=max_generator_grade);
    # now global variable __W contains 'pure' Wp
    T := table([seq(__W[j]=j, j=1..nops(__W))]);
    cc := [seq(homv(w, ex, [`$`(0, nops(w)), 1]), w=Wp)];
    if W[1] = [0] then
        c1 := wcoeff([s[1]], ex);
        if exact<>`none` then
            r1 := op(exact([0]));
        end;
        W := W[2..-1];
    else
        c1 := NULL;
        r1 := NULL;
    end if;

    r:=[c1, 
     seq(cc[T[[0$p-`if`(k=1,add(w),0)-nops(w),op(w)]]][p-`if`(k=1,add(w),0)-nops(w)+1], w=W),
     seq(cc[j][1], j=1..nops(Wp))];

    if exact<>`none` then
       rr := [r1, op(exact(W)), op(exact(__W))];
       r := r - rr;
    end if;
    r
end proc;


########################################
#Algorithm from
#  J. Sawada, F. Ruskey, Generating Lyndon brackets. An addendum to: Fast algorithms 
#  to generate necklaces, unlabeled necklaces and irreducible polynomials over GF(2),
#  J. Algorithms 46 (2003) 21–26

lyndon_bracket := proc(l::integer, r::integer, trafo::boolean)
    global __a, __split:
    if l=r then
        if trafo and __a[l+1]<>0 then
            return NULL
        else
            return __a[l+1]
        end if
    elif trafo and __a[l+1]=0 and __a[l+2..r+1]=[1$r-l] then
        return r-l
    else        
        return [lyndon_bracket(l,__split[l,r]-1, trafo),
            lyndon_bracket(__split[l,r], r, trafo)]
    end if
end proc;

genLB := proc (k::integer, n::integer, t::integer, trafo::boolean, mg::{integer, infinity})
    global __p, __a, __split, __B;
    local q, i, j;
    if t>n then
        if n=__p[1] then
            if not trafo or max(lyndon_transform(__a[2..n+1]))<mg then
                __B := [op(__B), lyndon_bracket(1, n, trafo)]
            end
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
            genLB(k, n, t+1, trafo, mg);
            __p := q
        end do
    end if
end proc;

convert_commutator := proc(s::{list(Generator), symbol}, c)
    if type(c,integer) then
        return s[c+1]
    else
        #return Physics[Commutator](convert_commutator(s, op(1, c)), 
        #                           convert_commutator(s, op(2, c)))
        return SimpleCommutator(convert_commutator(s, op(1, c)), 
                                convert_commutator(s, op(2, c)))
    end if
end proc;

lyndon_basis := proc(s::{integer, list(Generator), symbol}, q::{integer, list(integer)},
                     {max_generator_grade::{integer, infinity}:=infinity})
    local trafo, qq, n, k, b;
    global __a, __p, __split, __B;

    if type(s, list(Generator)) then
        k := nops(s)
    elif type(s, symbol) then
        k := 1
    else
        k := s
    end if;

    if type(q, integer) then
        qq := [q]
    else
        qq := q
    end;

    __B := [];
    trafo := k<2;

    for n in qq do
        __a := [0$n+1];
        __p := [1$n];
        __split := array(1 .. n, 1 .. n, [[0$n]$n]);
        genLB( `if`(trafo, 2, k), n, 1, trafo, max_generator_grade)
    end do;

    if type(s, integer) then
       return __B
    else
        return [seq(convert_commutator(s, b), b=__B)]
    end if
end proc;


########################################
#Implemented by H. Hofstätter after the method described in
#  E.S. Chibrikov, A right normed basis for free Lie algebras
#  and Lyndon-Shirshov words, Journal of Algebra 302 (2006) 593–612

lexless := proc (a::(list(integer)), b::(list(integer))) 
    if a=b then
        return false
    else
        return lexorder(convert([seq(x+1,x=a)], bytes), convert([seq(x+1,x=b)], bytes)) 
    end if
end proc;

sort_lexorder := proc (W::(list(list(integer)))) 
    # see https://www.mapleprimes.com/posts/40639-Ordering-A-List-Of-Lists#comment75122
    local Ws; 
    Ws := [seq(convert([seq(x+1, x = w)], bytes), w = W)];
    Ws := sort(Ws, lexorder); 
    [seq([seq(x-1, x = convert(w, bytes))], w = Ws)]
end proc;

invperm := proc(a::list(integer))
    local j;
    b := [0$nops(a)];
    for j from 1 to nops(a) do
        b[a[j]] := j
    end do;
    b
end proc;

reverse := proc(a::list(integer))
    local j;
    [seq(a[i], i=nops(a)..1,-1)]
end proc;

analyze_lyndon_word := proc(w::list(integer))
    q := max(w);
    A := table([seq([i]=i, i=1..q)]); 
    w1 := [];
    
    lw := nops(w);
    s := 1;
    m1 := 1;
    m2 := 0;
    
    # get a
    a := min(w);
    
    #get av
    s := s+1;
    while s<=lw and w[s]<>a do
        s := s+1
    end do;
    v := w[2..s-1];
    av := [a,op(v)];
    lav := nops(av);  
    while s<=lw do
        if m2<>0 then # do not change m2 in 1st iteration
            m1 := s
        end if;
        # get n
        n := 0;
        while s+lav<=lw and w[s+lav]=a and w[s..s+lav-1]=av do 
            s := s+lav;
            n := n+ 1
        end do;
        s := s+1;
    
        #get uu
        if member(a, w[s..-1], 'k') then
            k := k+s-1;
            uu := w[s..k-1];
            s := k
        else
            uu := w[s..-1];
            s := lw+1
        end if;
        #do something with uu 
        j := 1;
        while not (lexless(v,uu[1..j]) and not lexless(v,uu[1..j-1])) do
            j := j+1
        end do;
        u := uu[1..j];
        u1 := uu[j+1..-1];
        m2 := s-nops(u1)-1;
        if assigned(A[w[m1..m2]]) then
            x := A[w[m1..m2]]
        else
            q := q+1;
            A[w[m1..m2]] := q;
            x := q
        end if;
        w1 := [op(w1), x, op(u1)]
    end do;  
    pp := invperm([seq(A[x], x=sort_lexorder([indices(A, `nolist`)]))]);
    w2 := [seq(pp[x], x=w1)];
    tt := [[]$q];
    for xy in indices(A, 'pairs') do
        tt[pp[op(2,xy)]] := op(1,xy);
    end do;    
    w2, tt
end proc;

lyndon2rightnormed := proc(w::list(integer))
    aa := min(w);
    k := 0; # number of occurences of a in w
    for x in w do
        if x=aa then
            k := k+1
        end if
    end do;
    if k=1 then
        return reverse(w)
    end if;
    w_1, tt := analyze_lyndon_word(w);
    u_1 := lyndon2rightnormed(w_1);
    y := tt[u_1[-1]];
    a := y[1]; 
    member(a, y[2..-1], 'k0'); 
    k0 := k0+1;
    member(a, reverse(y), 'k1'); 
    k1 := nops(y)-k1+1;
    v := y[2..k0-1];
    avn := y[k0..k1-1];
    u1 := y[k1+1..-1];
    [op(map(op,tt[u_1[1..-2]])), op(avn), a, op(u1), op(reverse(v)), a]
end proc;

rightnormed_word2commutator := proc(w::list(integer))
    local j;
    b := w[-1];
    for j from nops(w)-1 to 1 by -1 do
        b := [w[j], b];
    end do;
    b
end proc;

rightnormed_basis := proc(s::{integer, list(Generator), symbol}, q::{integer, list(integer)},
                          {max_generator_grade::{integer, infinity}:=infinity})
    local k, B, w;

    if type(s, list(Generator)) then
        k := nops(s)
    elif type(s, symbol) then
        k := 1
    else
        k := s
    end if;

    B := [seq(rightnormed_word2commutator(
              lyndon2rightnormed(w)), w=lyndon_words(k, q, ':-max_generator_grade'=max_generator_grade))];

    if type(s, integer) then
       return B
    else
       return [seq(convert_commutator(s, b), b=B)]
    end if
end proc;

########################################
lyndon_transformation_matrix := proc(s::{integer, list(Generator), symbol}, q::{integer, list(integer)},
                          {max_generator_grade::{integer, infinity}:=infinity,
                           rightnormed::boolean:=false})
    local homv1, wcoeff1, k, W, B, blocks, i, j, c, x, T, b;

    homv1 := proc (w::(list(integer)), ex::{integer, list}, v::(list(integer))) 
        if type(ex, integer) then 
            return [seq(`if`(op(i, w) = ex, v[i+1], 0), i = 1 .. nops(w)), 0] 
        else 
            return homv1(w, op(1, ex), homv1(w, op(2, ex), v))-homv1(w, op(2, ex), homv1(w, op(1, ex), v)) 
        end if 
    end proc; 

    wcoeff1 := proc (w::(list(integer)), ex::{integer, list}) 
        homv1(w, ex, [`$`(0, nops(w)), 1])[1] 
    end proc;

    if type(s, list(Generator)) then
        k := nops(s)
    elif type(s, symbol) then
        k := 1
    else
        k := s
    end if;

    W := lyndon_words(k, q, ':-max_generator_grade'=max_generator_grade);
    if rightnormed then
        B := rightnormed_basis(k, q, ':-max_generator_grade'=max_generator_grade);
    else
        B := lyndon_basis(k, q, ':-max_generator_grade'=max_generator_grade);
    end if;

    blocks := table([seq(x = [], x = op({seq(sort(w), w = W)}))]); 
    for i to nops(W) do 
        c := sort(W[i]); 
        blocks[c] := [op(blocks[c]), i] 
    end do; 
    blocks := [entries(blocks, 'nolist')];

    T := array([`$`([`$`(0, nops(W))], nops(W))]); 
    for b in blocks do 
        for i to nops(b) do 
            for j to `if`(rightnormed, nops(b), i) do 
                T[b[i], b[j]] := wcoeff1(W[b[i]], B[b[j]]) 
            end do
        end do
    end do;
    
    T
end proc;


########################################
rhs_legendre := proc(W::list)
    local W1, x, p, w, L, l, s, c, k, T, v;
    if type(W[1], Word) then
        W1 := [seq(map(grade, [op(w)]), w in W)];
    else
        W1 := [seq([seq(x+1, x in w)], w in W)];
    end if;
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
