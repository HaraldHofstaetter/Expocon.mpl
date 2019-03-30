# Expocon.mpl

A Maple package for the generation of order conditions for the construction of exponential integrators.

>[1] [W. Auzinger](http://www.asc.tuwien.ac.at/~winfried), [H. Hofstätter](http://www.harald-hofstaetter.at), [O. Koch](http://othmar-koch.org), [An Algorithm for Computing Coefficients of Words in Expressions Involving Exponentials and its Application to the Construction of Exponential Integrators](), submitted.

>[2] [H. Hofstätter](http://www.harald-hofstaetter.at), [Order conditions for exponential integrators](https://arxiv.org/pdf/1902.11256), submitted. 


[`phiv`](https://github.com/HaraldHofstaetter/Expocon.mpl/blob/master/src/Expocon.mpl#L65)

[`wcoeff`](https://github.com/HaraldHofstaetter/Expocon.mpl/blob/master/src/Expocon.mpl#L111)

```maple
with(Physics):
read "/path/to/Expocon.mpl":
```
```maple
Setup(noncommutativeprefix = {A, B}):
X := exp((1/2)*B)*exp(A)*exp((1/2)*B)-exp(A+B):
W := [[A], [B], [A, A], [A, B], [B, A], [B, B], 
     [A, A, A], [A, A, B], [A, B, A], [A, B, B], 
     [B, A, A], [B, A, B], [B, B, A], [B, B, B]]:
seq(wcoeff(w, X), w in W);
```
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?0,0,0,0,0,0,0,\frac{1}{12},\frac{-1}{6},\frac{-1}{24},\frac{1}{12},\frac{1}{12},\frac{-1}{24},0"/></p>


<p align="center">
<img src="https://latex.codecogs.com/gif.latex?e^{\frac{1}{2}B}e^{A}e^{\frac{1}{2}B}-e^{A+B}=\left.\tfrac{1}{12}AAB-\tfrac{1}{6}ABA-\tfrac{1}{24}ABB+\tfrac{1}{12}BAA+\tfrac{1}{12}BAB-\tfrac{1}{24}BBA+\dots\right.">
</p>

<p align="center">
<img src="https://latex.codecogs.com/gif.latex?e^{\frac{1}{2}B}e^{A}e^{\frac{1}{2}B}-e^{A+B}=\tfrac{1}{12}[A,[A,B]]-\tfrac{1}{24}[[A,B],B]+\dots">
</p>

```maple
Setup(noncommutativeprefix = {A, B});
C := Commutator;
X := exp(b*B)*exp(a*A)*exp(c*B+d*C(B, C(A, B)))*exp(a*A)*exp(b*B)-exp(A+B);
W := lyndon_words([A, B], [1, 3]);
```
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?[[A],[B],[A,A,B],[A,B,B]]">
</p>

```maple
eqs := [seq(simplify(wcoeff(w, X)), w in W)];
```
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?eqs:=\left[-1+2a,-1+2b+c,-\frac{1}{6}+2a^2b+\frac{1}{2}a^2c,-\frac{1}{6}+\frac{1}{2}ac^2+acb+ab^2-d\right]"/></p>

```maple
sol := solve(eqs);
```
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?sol:=\left\{a=\frac{1}{2},b=\frac{1}{6},c=\frac{2}{3},d=\frac{1}{72}\right\}"/></p>

```maple
W5 := lyndon_words([A, B], [5]);
``` 
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?W5:=[[A,A,A,A,B],[A,A,A,B,B],[A,A,B,A,B],[A,A,B,B,B],[A,B,A,B,B],[A,B,B,B,B]]"/></p>

```maple
B5 := lyndon_basis([A, B], [5]);
```
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?B5:=[[A,[A,[A,[A,B]]]],[A,[A,[[A,B],B]]],[[A,[A,B]],[A,B]],[A,[[[A,B],B],B]],[[A,B],[[A,B],B]],[[[[A,B],B],B],B]]"/></p>
          
```maple          
T5 := Matrix([seq([seq(wcoeff(w, b), b in B5)], w in W5)]);
```
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?T5:=\left[\begin{array}{rrrrrr}1&0&0&0&0&0\\0&1&0&0&0&0\\0&-2&1&0&0&0\\0&0&0&1&0&0\\0&0&0&-3&1&0\\0&0&0&0&0&1\end{array}\right]"/></p>
              
```maple              
c_w := [seq(wcoeff(w, subs(sol, X)), w in W5)];
```
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?c\_w:=\left[\frac{1}{2880},\frac{-7}{8640},\frac{1}{480},\frac{7}{12960},\frac{-1}{720},\frac{-41}{155520}\right]"/></p>

```maple              
c_b := evalm(`&*`(LinearAlgebra[MatrixInverse](T5), c_w));
```
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?c\_b:=\left[\frac{1}{2880},\frac{-7}{8640},\frac{1}{2160},\frac{7}{12960},\frac{1}{4320},\frac{-41}{155520}\right]"/></p>

