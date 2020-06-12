This is implementation of the calculus of *Coinductive Uniform Proofs (CUP)* and the heuristics for coinductive theory exploration.

The prototype implements the full cycle of *proof-search -- proof failure -- theory exploration -- proof recovery*.
That is, the user interaction with the tool consists of the following steps:


* The user formulates a Horn clause theory (a program) and a ``Desired Goal'', see examples in Fig.~\ref{fig:P&G}
 

* On the first proof attempt, only the rules of the calculus of coinductive uniform proofs are applied (this includes the coinductive rules such as $\Cofix$ but excludes $\Cut$.)

\item If such proof attempt fails, then a series of heuristics described in \S~\ref{sec:irreg}, \S~\ref{sec:exist} and \ref{ap:Fu} is applied, with the purpose of finding a suitable coinduction hypothesis and possibly also to discover a required fixed point term. The discovered coinduction hypotheses are shown in Fig.~\ref{fig:CH}.

 
    


\item The obtained coinduction hypotheses are then themselves proven using the rules of the calculus of coinductive uniform proofs. Those that cannot be proven are discarded. In particular, Fig.~\ref{fig:CH} shows only the coinduction hypotheses that were validated by the tool. 
  
\item The coinduction hypotheses that yield coinductive uniform proofs are added to the logic program in question (conservativity and coinductive soundness of such program transformation is proven in ~\cite{BasoldKL19-2})
  and the tool makes another attempt to prove the ``Desired Goal''.

\item Finally, the tool reports success or failure, and in the former case it declares the generated coinduction hypotheses and term substitutions that were used in order to prove the  ``Desired Goal''. All the desired goals listed in Fig.\ref{fig:P&G} were proven by the tool, with the help of the
  coinduction hypotheses, as listed in Fig.~\ref{fig:CH}.
  
  \end{itemize}

  \begin{figure}[t]
\[ \begin{array}{|l|l|l|}
  \hline
  \# & \texttt{Program} & \texttt{Desired Goal} \\
  \hline
    1 &
    \begin{array}{ll}
      \kappa_{fg} &: \all{x,y}  p(x,y) \impl p(f(y), g(x))\\
    \end{array}
    & \exist{x, y} p(x,y) \\
  \hline
    2 &
    \begin{array}{ll}
      \kappa_{fg} &: \all{x,y}  p(x,y) \impl p(f(x,y), g(x,y))\\
    \end{array}
    & \exist{x, y} p(x,y) \\
  \hline
    3 &
    \begin{array}{ll}
      \kappa_{\stream0} &: \all{x}  \stream(x) \impl \stream(\scons(0, x))\\
    \end{array}
    & \exist{x} \stream(x) \\
  \hline
    4 &
    \begin{array}{ll}
      \kappa_{\stream01} &: \all{x} \stream_{OZ}(x) \impl \stream_{ZO}(\scons(0, x))\\
      \kappa_{\stream10} &: \all{x} \stream_{ZO}(x) \impl \stream_{OZ}(\scons(1, x))\\
    \end{array}
    & \exist{x} \stream_{ZO}(x) \\
  \hline
    5 &
    \begin{array}{ll}
      \kappa_{u} &: \all{x}  p(f(x)) \impl p(x)\\
    \end{array}
    & p(a) \\
  \hline
    6 &
    \begin{array}{ll}
      \kappa_{i1} &: \all{x}  p(f(x)) \conj q(x) \impl p(x) \\
      \kappa_{i2} &: q(a) \\
      \kappa_{i3} &: \all{x}  q(x) \impl q(f(x))\\
    \end{array}
    & p(a) \\
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

  \begin{figure}[t]
\[ \begin{array}{|l|l|}
  \hline
  \# & \texttt{Generated coinduction hypothesis} \\
  \hline
    1
    & p( f(\fix[x] g(f(x)))  ,  g(f(\fix[x] g(f(x)))) ) \\
  \hline
    2 &
    \begin{array}{l}
      p( f(\fix[x] f(x, r), r), g(\fix[x] f(x, r), r) ) \\
      \qquad \texttt{where  } r = \fix[y] g(\fix[z] f(z, y), y)
    \end{array}     \\
  \hline
    3 &
    \stream( \scons(0, \fix[x] \scons(0, x)) ) \\
  \hline
    4 &
    \stream_{ZO}( \scons(0, \scons(1, \fix[x] \scons(0, \scons(1, x)))) ) \\
  \hline
    5 &
    \all{x} p(x) \\
  \hline
    6 &
    \all{x} q(x) \impl p(x) \\
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
