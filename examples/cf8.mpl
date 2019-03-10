with(Physics):
read "/home/hofi/Maple/Expocon.mpl/src/Expocon.mpl":
with(Expocon):

Setup(noncommutativeprefix = {A}):

S := exp(A[1]*f11-A[2]*f12+A[3]*f13-A[4]*f14)*
     exp(A[1]*f21-A[2]*f22+A[3]*f23-A[4]*f24)*
     exp(A[1]*f31-A[2]*f32+A[3]*f33-A[4]*f34)*
     exp(A[1]*f41-A[2]*f42+A[3]*f43-A[4]*f44)*
     exp(A[1]*f41+A[2]*f42+A[3]*f43+A[4]*f44)*
     exp(A[1]*f31+A[2]*f32+A[3]*f33+A[4]*f34)*
     exp(A[1]*f21+A[2]*f22+A[3]*f23+A[4]*f24)*
     exp(A[1]*f11+A[2]*f12+A[3]*f13+A[4]*f14):

W12 := lyndon_words(A, [1, 3, 5, 7], max_generator_grade = 2):
rhs12 := rhs_legendre(W12):
vars12 := [f11, f21, f31, f41, f12, f22, f32, f42]:

W3 := [seq(`if`(member(A[3], w), w, NULL), w in lyndon_words(A, [1, 3, 5, 7], max_generator_grade = 3))]:
rhs3 := rhs_legendre(W3):
vars3 := [f13, f23, f33, f43]:

W4 := [seq(`if`(member(A[4], w), w, NULL), w in lyndon_words(A, [1, 3, 5, 7], max_generator_grade = 4))]:
rhs4 := rhs_legendre(W4):
vars4 := [f14, f24, f34, f44]:

W := [op(W12), op(W3), op(W4)]:
RHS := [op(rhs12), op(rhs3), op(rhs4)]:

W_lem := lyndon_words(A, [9], max_generator_grade = 5):
rhs_lem := rhs_legendre(W_lem):

eqs12 := [seq(expand(wcoeff(w, S)), w in W12)] - rhs12:

Digits := 200:

sols12 := solve(eqs12, vars12):
save sols12,"cf8_sols12.m":
#read "cf8_sols12.m":

FF := seq(evalf(allvalues(sol)), sol in sols12):
save FF, "cf_FF.m":
#read "cf8_FF.m":

k := 0:

interface(screenwidth = 160):

for F12 in FF do
    k := k+1:
    printf("#%3a ###################################\n",k):

    eqs3 := [seq(expand(wcoeff(w, subs(F12, S))), w in W3[2..5])]-rhs3[2..5]:
    F3 := op(solve(eqs3, vars3)):

    eqs4 := [seq(expand(wcoeff(w, subs(F12, F3, S))), w in W4[1..4])]-rhs4[1..4]:
    F4 := op(solve(eqs4, vars4)):

    err := max(map(abs,([seq(wcoeff(w, subs(F12, F3, F4, S)), w in W)]-RHS))):
    lem := evalf(norm(Vector([seq(wcoeff(w, subs(F12, F3, F4, S)), w in W_lem)]-rhs_lem), 2), 10);

    for y in [op(F12), op(F3), op(F4)] do 
        lprint(evalf(op(2, y), 50)): 
    end do:
    printf("# err = %.5e  LEM = %.5e\n", err, lem):
end do:


