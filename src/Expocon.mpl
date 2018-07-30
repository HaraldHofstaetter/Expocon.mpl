Expocon := module()

option package;
export Generator, Word, grade, hom, wcoeff, lyndon_words,
       rhs_legendre;
global `type/Generator`, `type/Word`, `print/Word`, `print/hom`;
local grade_gen, grade_word, lyndon_words_int, lyndon_words_list,
      lyndon_words_non_auto, lyndon_transform;

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

lyndon_words_int := proc (s::integer, n::integer, { [o1, all_lower_terms]::boolean := true, [o2, odd_terms_only]::boolean := false }) 
    local w, k, m, W; 
    option overload; 
    w := [1, seq(0, k = 1 .. n-1)]; 
    k := 1; 
    W := []; 
    if (o1 or k = n) and (not o2 or type(k, odd)) then 
        W := [op(W), w[1 .. k]] 
    end if; 
    while 1 < k or w[1] < s do 
        m := k; 
        while k < n do 
            w[k+1] := w[k-m+1]; 
            k := k+1 
        end do; 
        while 0 < k and w[k] = s do 
            k := k-1 
        end do; 
        w[k] := w[k]+1; 
        if (o1 or k = n) and (not o2 or type(k, odd)) then 
            W := [op(W), w[1 .. k]] 
        end if 
    end do; 
    return sort(W, proc (x, y) options operator, arrow; nops(x) <= nops(y) end proc) 
end proc;

lyndon_words_list := proc (S::list(Generator), n::integer, { all_lower_terms::boolean := true, odd_terms_only::boolean := false }) 
    local W; 
    option overload; 
    W := lyndon_words_int(nops(S), n, o1 = all_lower_terms, o2 = odd_terms_only); 
    [seq(Word(seq(op(W[i, j], S), j = 1 .. nops(W[i]))), i = 1 .. nops(W))] 
end proc;

lyndon_transform := proc (w::(list(integer))) 
    local w1, c, x; 
    w1 := []; 
    c := 1; 
    for x in w[2 .. -1] do 
        if x = 2 then 
            c := c+1 
        else 
            w1 := [op(w1), c]; 
            c := 1 
        end if 
    end do; 
    w1 := [op(w1), c]; 
    w1 
end proc;

lyndon_words_non_auto := proc (A::symbol, n::integer, { all_lower_terms::boolean := true, odd_terms_only::boolean := false, max_generator_grade::integer:=n }) 
    local W; 
    option overload; 
    W := map(lyndon_transform,
             lyndon_words_int(2, n, o1 = all_lower_terms, o2 = odd_terms_only)[2..-1]); 
    if max_generator_grade<n then
         W := remove(w->max(w)>max_generator_grade, W)
    end if;
    [seq(Word(seq(A[x], x in w)), w in W)]
end proc;

lyndon_words := overload([lyndon_words_int, lyndon_words_list, lyndon_words_non_auto]);

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
