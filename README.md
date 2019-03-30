# Expocon.mpl

A Maple package for the generation of order conditions for the construction of exponential integrators.

>[H. Hofstätter](http://www.harald-hofstaetter.at), [Order conditions for exponential integrators](https://arxiv.org/pdf/1902.11256), submitted. 

```maple
> with(Physics):
> read "/path/to/Expocon.mpl":
```
```maple
> Setup(noncommutativeprefix = {A, B}):
> X := exp((1/2)*B)*exp(A)*exp((1/2)*B)-exp(A+B):
> W := [[A], [B], [A, A], [A, B], [B, A], [B, B], 
       [A, A, A], [A, A, B], [A, B, A], [A, B, B], 
       [B, A, A], [B, A, B], [B, B, A], [B, B, B]]:
> seq(wcoeff(w, X), w in W);
```
<p align="center">
<img src="https://latex.codecogs.com/gif.latex?0,0,0,0,0,0,0,\frac{1}{12},\frac{-1}{6},\frac{-1}{24},\frac{1}{12},\frac{1}{12},\frac{-1}{24},0"/></p>

<p align="center">
<img src="https://latex.codecogs.com/gif.latex?e^{\frac{1}{2}B}e^{A}e^{\frac{1}{2}B}-e^{A+B}">
<img src="https://latex.codecogs.com/gif.latex?=\tfrac{1}{12}AAB-\tfrac{1}{6}ABA-\tfrac{1}{24}ABB+\tfrac{1}{12}BAA+\tfrac{1}{12}BAB-\tfrac{1}{24}BBA+\dots">
</p>

<p align="center">
<img src="https://latex.codecogs.com/gif.latex?e^{\frac{1}{2}B}e^{A}e^{\frac{1}{2}B}-e^{A+B}=\tfrac{1}{12}[A,[A,B]]-\tfrac{1}{24}[[A,B],B]+\dots">
</p>
