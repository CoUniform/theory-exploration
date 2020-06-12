<h4> Implementation of coinductive Uniform proofs and coinductive theory exploration </h4>

This is implementation of the calculus of *Coinductive Uniform Proofs (CUP)* and the heuristics for coinductive theory exploration. It accompanies the draft [2].

The prototype implements the full cycle of *proof-search -- proof failure -- theory exploration -- proof recovery*.
That is, the user interaction with the tool consists of the following steps:


* The user formulates a Horn clause theory (a program) and a ``Desired Goal'', see examples below.
 

* On the first proof attempt, only the rules of the calculus of coinductive uniform proofs are applied (this includes the coinductive rules such as *Cofix* but excludes *Cut*.

* If such proof attempt fails, then a series of heuristics is applied, with the purpose of finding a suitable coinduction hypothesis and possibly also to discover a required fixed point term.    

* The obtained coinduction hypotheses are then themselves proven using the rules of the calculus of coinductive uniform proofs. Those that cannot be proven are discarded. 
  
* The coinduction hypotheses that yield coinductive uniform proofs are added to the logic program in question (conservativity and coinductive soundness of such program transformation is proven in [1])
  and the tool makes another attempt to prove the ``Desired Goal''.

* Finally, the tool reports success or failure, and in the former case it declares the generated coinduction hypotheses and term substitutions that were used in order to prove the  ``Desired Goal''. 
  
<h3> Examples: </h3>  
  
|    Program                                                 |  Desired Goal      | Discovered Coinduction Hypothesis                     |
|:----------------------------------------------------------:|-------------------:|:-----------------------------------------------------|
| kappa_fg: forall x,y.  p(x,y) -> p(f(y), g(x))             | exist x, y. p(x,y) | p( f(fix[x] g(f(x)))  ,  g(f(fix[x] g(f(x)))) ) |
| kappa_fg: forall x,y.  p(x,y) -> p(f(x,y), g(x,y))         | exist x, y. p(x,y) |   p( f(fix[x] f(x, r), r), g(fix[x] f(x, r), r) ), where r = fix[y] g(fix[z] f(z, y), y)
| kappa_stream0: forall x.  stream(x) -> stream(scons(0, x)) | exist x. stream(x) | stream(scons(0, fix[x] scons(0, x)) )               | 
| kappa_stream01: forall x. stream_OZ (x) -> stream_ZO (scons(0, x)); 
kappa_stream10: forall x. stream_ZO (x) -> stream_OZ(scons(1, x)) |  exist x. stream_ZO (x)  |  stream_ZO( scons(0, scons(1, fix[x] scons(0, scons(1, x)))) ) |
|kappa_u: forall x.  p(f(x)) -> p(x) | p(a) |    forall x. p(x) |
| kappa_i1: forall x.  p(f(x)) & q(x) -> p(x) 
  kappa_i2: q(a) 
  kappa_i3: forall x.  q(x) -> q(f(x))  |  p(a)  | forall x. q(x) -> p(x) |
      
  \hline
    7 &
    \begin{array}{ll}
      \kappa_{from} &: \all{x, y} \fromP(s(x), y) \impl \fromP(x, \scons(x, y)) \\
    \end{array}
    & \exist{x, y} \fromP(x, y) \\
  \hline
    8 &
    \begin{array}{ll}
      \kappa_{from} &: \all{x, y} \fromP(s(x), y) \impl \fromP(x, \scons(x, y)) \\
    \end{array}
    & \exist{y} \fromP(0, y) \\
  \hline
    9 &
    \begin{array}{ll}
      \kappa_{fib} &: \all{x, y, z} \fib(y, \plusFun(x, y), z) \impl \fib(x, y, \scons(x, z)) \\
    \end{array}
    & \exist{x, y, z} \fib(x, y, z) \\
  \hline
    10 &
    \begin{array}{ll}
      \kappa_{fib} &: \all{x, y, z} \fib(y, \plusFun(x, y), z) \impl \fib(x, y, \scons(x, z)) \\
    \end{array}
    & \exist{z} \fib(0, 1, z) \\
  \hline
\end{array} \]
  \caption{Evaluation: Logic programs and desired goals provided to the tool.}
    \label{fig:P&G}
  \end{figure}


 
    6 &
    \\
  \hline
    7 &
    \begin{array}{l}
      \fromP(\infty, \scons(\infty, \fix[y] \scons(\infty, y))) \\
      \qquad \texttt{where  } \infty = \fix[x] s \, x
    \end{array}     \\
  \hline
    8 &
    \all{x} \fromP(n, (\fix[f] \lam{x} \scons(x, f \, (s(x)))) \, n)  \\
  \hline
    9 &
    \begin{array}{l}
      \fib \, \infty \, \infty \,
      (\scons \, \infty \, (\fix[z] (\scons \, \infty \, z))) \\
      \qquad \texttt{where  } \infty = \fix[x] \plusFun \, x \, x
    \end{array}     \\
  \hline
    10
     & \begin{array}{l}
         \all{x \, y} \fib \, x \, y \, (f \, x \, y) \\
         \qquad \texttt{where  }
         f = \fix[f] \lam{u \, v} \scons \, u \, (f \, v \, (\plusFun \, u \, v))
       \end{array}
     \\
     \hline
\end{array} \]
  \caption{Coinductive Hypotheses discovered by the tool according to the heuristics described in  \S~\ref{sec:irreg} and \ref{ap:Fu}. We shorten the fixed point term $\fix[x] s(x)$ by using notation $\infty$.}
    \label{fig:CH}
  \end{figure}

<h3> To install: </h3>

Use `make` to compile and `./theory_exp ` to run the tool

<h3> References </h3>
[1] H. Basold, E. Komendantskaya, Y. Li: Coinduction in Uniform: Foundations for Corecursive Proof Search with Horn Clauses. ESOP 2019 (28th European Symposium on Programming), 8-11 April 2019, Prague.

[2] E.Komendantskaya, D.Rozplokhas, H.Basold: The New Normal: We cannot Eliminate the Cuts, but we can Explore them. Draft. 2020. 
