\section{Renamingless Capture-Avoiding Substitution}
\label{sec:interpretation}

We present a simple technique for capture avoiding substitution, which avoids the need to rename bound variables.
To demonstrate that the technique is about as simple to implement as substitution for closed terms (i.e., terms with no free variables, for which variable capture is not a problem), we first implement a standard substitution-based definitional interpreter for a language with closed, call-by-value $\lambda$ expressions.

\subsection{Interpreting Closed Expressions}
\label{sec:interpreting-closed}

Below left is a data type for the abstract syntax of a language with $\lambda$s, variables, applications, and numbers.
On the right is the substitution function for the language.
The function binds three parameters: (1) the variable name (|String|) to be substituted, (2) the expression the name should be replaced by, and (3) the expression in which substitution happens.
\\
%format Expr0
%format Lam0
%format Var0
%format App0
%format Num0
\begin{minipage}{0.295\linewidth}
\begin{code}
data Expr0
  =  Lam0 String Expr0
  |  Var0 String
  |  App0 Expr0 Expr0
  |  Num0 Int
\end{code}
%if False
\begin{code}
  deriving Show
\end{code}
%endif
\end{minipage}
\vline
\begin{minipage}{0.695\linewidth}
%format subst0
%format e1
%format e1'
%format e2
\begin{code}
subst0 :: String -> Expr0 -> Expr0 -> Expr0
subst0 x  s  (Lam0 y e)    |  x == y     = Lam0 y e
                           |  otherwise  = Lam0 y (subst0 x s e)
subst0 x  s  (Var0 y)      |  x == y     = s
                           |  otherwise  = Var0 y
subst0 x  s  (App0 e1 e2)  =  App0 (subst0 x s e1) (subst0 x s e2)
subst0 _  _  (Num0 z)      =  Num0 z
\end{code}
\end{minipage}
%
The main interesting case is the case for |Lam0|.
There are two sub-cases, declared using \emph{guards} (the Boolean expressions after the vertical bar).
The first sub-case is when the variable being substituted matches the bound variable (|x == y|).
Since the inner variable shadows the outer, the substitution is not propagated into the body.
In the other case (|otherwise|), the substitution is propagated.
This other case relies on an implicit assumption that the expression being substituted by |x| does not have |y| as a free variable.
%
%format interp0
%
If we violate this assumption, the substitution function and interpreter |interp0| on the left below is not going to be capture avoiding.
Below right is an example invocation of the interpreter.\\
%
\begin{minipage}{0.495\linewidth}
\begin{code}
interp0 :: Expr0 -> Expr0
interp0 (Lam0 x e)    = Lam0 x e
interp0 (Var0 _)      = error "Free variable"
interp0 (App0 e1 e2)  = case interp0 e1 of
  Lam0 x e  -> interp0 (subst0 x (interp0 e2) e)
  _         -> error "Bad application"
interp0 (Num0 z)      = Num0 z
\end{code}
\end{minipage}
\vline
\begin{minipage}{0.495\linewidth}
< > interp0 (App0  (Lam0 "x" (Var0 "x"))
<                  (Num0 42))
< Num0 42
\end{minipage}
%
% While the |interp0| function raises an error if it is called on a |Var0|, we can still get variable capture for expressions with free variables, such as $(\lambda x.\, (\lambda y.\, x 1) 2))\ (\lambda z. y)$, which \emph{should} interpret to an expression with a free variable; but which interprets to 1 using |interp0|.

\subsection{Intermezzo: Capture-Avoiding Substitution Using Renaming}
\label{sec:intermezzo}

%format subst01 = subst "_{01}"

The substitution function |subst0| relies on an implicit assumption that expressions are closed; i.e., do not contain free variables.
If we want to support \emph{open expressions} (i.e., expressions that may contain free variables), we must take care to avoid variable capture.
A traditional approach~\cite{Plotkin75} is to rename variables during interpretation, as implemented by the function |subst01| whose cases are the same as |subst0|, except for the |Lam0| case:
%
%format gray (x) = "\colorbox{black!10}{$" x "$}"
%if False
\begin{code}
gray = id
\end{code}
%endif
%
%if False
\begin{code}
subst01 :: String -> Expr0 -> Expr0 -> Expr0
\end{code}
%endif
\begin{code}
subst01 x  s  (Lam0 y e)    |  x == y     = Lam0 y e
                            |  otherwise  =  let z = gray (fresh x y s e)
                                             in Lam0 z (gray (subst01 x s (subst01 y (Var0 z) e)))
\end{code}
%if False
\begin{code}
subst01 x  s  (Var0 y)      |  x == y     = s
                            |  otherwise  = Var0 y
subst01 x  s  (App0 e1 e2)  =  App0 (subst01 x s e1) (subst01 x s e2)
subst01 _  _  (Num0 z)      =  Num0 z
\end{code}
%endif
%
Here |fresh x y s e| is a function that returns a fresh identifier if $x \not\in FV(e)$ or $y \not\in FV(s)$, or returns $y$ otherwise.
%If $x \not\in FV(e)$ then $s$ will not appear in $e$ after substitution, so renaming is unnecessary.
%If $y \in FV(s)$, then we choose a fresh $z \not\in FV(s) \cup FV(e)$ such that free identifiers in $s$ are not captured.
%
%format fv0
%if False
\begin{code}
fresh :: String -> String -> Expr0 -> Expr0 -> String
fresh x y s e = let fvs = fv0 s
                    fve = fv0 e
                 in if (not (x `elem` fve) || not (y `elem` fvs))
                    then y
                    else freshify y (fvs ++ fve)

fv0 :: Expr0 -> [String]
fv0 (Lam0 x e) = filter ((/=) x) (fv0 e)
fv0 (Var0 x) = [x]
fv0 (App0 e1 e2) = fv0 e1 ++ fv0 e2
fv0 (Num0 _) = []

freshify :: String -> [String] -> String
freshify x ys = let x' = '#':x
                in if x' `elem` ys
                   then freshify x' ys
                   else x'

interp01 :: Expr0 -> Expr0
interp01 (Lam0 x e)    = Lam0 x e
interp01 (Var0 _)      = error "Free variable"
interp01 (App0 e1 e2)  = case interp01 e1 of
  Lam0 x e  -> interp01 (subst01 x (interp01 e2) e)
  _         -> error "Bad application"
interp01 (Num0 z)      = Num0 z

mkDeepApp :: Int -> Expr0
mkDeepApp n = go n (Lam0 "x" (Var0 "x"))
  where go n e | n <= 0 = App0 e (Num0 42)
        go n e = let x = "x" ++ show n
          in go (n - 1) (Lam0 x (App0 e (Var0 x)))
\end{code}
%endif
%
While this renaming based substitution strategy provides a relatively conceptually straightforward solution to the name capture problem, it requires an approach to generating fresh variables, and, since it performs two recursive calls to |subst01|, it is inherently less efficient than the substitution function from \cref{sec:interpreting-closed}---even in a lazy language like Haskell.
Furthermore, depending on how |fresh| is implemented, the interpreter may not preserve the names of $\lambda$-bound variables.
In the next section we introduce an simple alternative substitution strategy which does not rename or generate fresh variables, and which has similar efficiency as substitution for closed expressions.
% The substitution strategy is capture-avoiding for languages that do not evaluate under binders.


\subsection{Interpreting Open Expressions with Renamingless Substitution}
\label{sec:interpreting-open}

%format subst1
%format Expr1
%format Lam1
%format Var1
%format App1
%format Num1
%format Clo1 = "\colorbox{gray!30}{\textit{Clo}$_1$}"
%format interp1

Let us revisit the interpretation function |interp0| from \cref{sec:interpreting-closed}.
Because our interpreter eagerly applies substitutions whenever it can, and because evaluation always happens at the top-level, never under binders, we know the following.
Whenever the interpreter reaches an application expression $e_1\ e_2$, we know that \emph{any variable that occurs free in $e_2$ corresponds to a variable that was free to begin with}.
% The same goes for the expressions resulting from interpreting $e_2$.
We can exploit this knowledge in our interpreter and substitution function.
To this end, we introduce a dedicated expression form (the highlighted |Clo1| constructor below) which delimits expressions that have been closed under substitutions such that we never propagate substitutions past this closure delimiter:
\\
\begin{minipage}{0.295\linewidth}
\begin{code}
data Expr1
  =  Lam1 String Expr1
  |  Var1 String
  |  App1 Expr1 Expr1
  |  Num1 Int
  |  Clo1 Expr1
\end{code}
%if False
\begin{code}
  deriving Show
\end{code}
%endif
\end{minipage}
\vline
\begin{minipage}{0.695\linewidth}
%format subst1
\begin{code}
subst1 :: String -> Expr1 -> Expr1 -> Expr1
subst1 x  s  (Lam1 y e)    |  x == y     = Lam1 y e
                           |  otherwise  = Lam1 y (subst1 x s e)
subst1 x  s  (Var1 y)      |  x == y     = s
                           |  otherwise  = Var1 y
subst1 x  s  (App1 e1 e2)  =  App1 (subst1 x s e1) (subst1 x s e2)
subst1 _  _  (Num1 z)      =  Num1 z
subst1 _  _  (Clo1 e)      =  Clo1 e
\end{code}
\end{minipage}
%
Here |subst1| does not propagate substitutions into expressions delimited by |Clo1|.
The interpretation function |interp1| uses |Clo1| to close expressions before substituting (in the |App1| case), thereby avoiding name capture:
%
\begin{code}
interp1 :: Expr1 -> Expr1
interp1 (Lam1 x e)    = Lam1 x e
interp1 (Var1 x)      = Var1 x
interp1 (App1 e1 e2)  = case interp1 e1 of
  Lam1 x e  -> interp1 (subst1 x (Clo1 (interp1 e2)) e)
  e1'       -> App1 e1' (interp1 e2)
interp1 (Num1 z)      = Num1 z
interp1 (Clo1 e)      = e
\end{code}
%
Whereas |interp0| explicitly crashes when encountering a free variable or when attempting to apply a non-function to a number, |interp1| may return a ``stuck'' term in case it encounters a free variable or an application expression that attempts to apply a value other than a function.
The last case of |interp1| says that, when the interpreter encounters a closed expression, it ``unpacks'' the closure.
This unpacking will not cause accidental capture:
interpretation never happens under binders, so the only way the unpacked term can end up under a binder is via substitution.
However, |interp1| only calls substitution on terms closed with |Clo1|, thereby undoing the unpacking to prevent accidental capture.

To illustrate how |interp1| works, let us consider how to interpret $((\lambda f.\, \lambda y.\, f\ 0)\ (\lambda z.\, y)\ 1)$.
The rewrites below informally illustrate the interpretation process, where for brevity we use $\lambda$ notation instead of the corresponding constructors in Haskell and \colorbox{gray!30}{$\lfloor e \rfloor$} instead of |Clo1 e|:
%
\begin{align*}
      &|interp1|\ ((\lambda f.\, \lambda y.\, f\ 0)\ (\lambda z.\, y)\ 1) \\
  |==|\ &|interp1|\ ((\lambda y.\, \colorbox{gray!30}{$\lfloor (\lambda z.\, y) \rfloor$}\ 0)\ 1) \\
  |==|\ &|interp1|\ (\colorbox{gray!30}{$\lfloor (\lambda z.\, y) \rfloor$}\ 0) \\
  |==|\ &y
\end{align*}

Unlike the renaming based substitution strategy discussed in \cref{sec:intermezzo}, our renamingless substitution strategy does not require renaming or generating fresh variables.
Its efficiency is similar as substitution for closed expressions.
It also preserves the names of binders.
However, the renamingless substitution strategy in |subst1| and |interp1| relies on an assumption that evaluation does not happen under binders.

\subsection{Limitation: Renamingless Substitution Does Not Support Evaluation Under Binders}
\label{sec:renamingless-bad}

%format normalize1
%format subst11 = subst1
%format Expr11 = Expr1
%format Lam11 = Lam1
%format Var11 = Var1
%format App11 = App1
%format Num11 = Num1
%format Clo11 = "\textit{Clo}_1"

The renamingless substitution strategy from \cref{sec:interpreting-open} assumes that terms under a |Clo11| have been closed under \emph{all substitutions of variables bound in the context}.
Interpretation strategies that evaluate under binders violate this assumption.
For example, consider the interpreter given by |normalize1| whose highlighted recursive call performs evaluation under a $\lambda$ binder:
%
%if False
\begin{code}
data Expr11
  =  Lam11 String Expr11
  |  Var11 String
  |  App11 Expr11 Expr11
  |  Num11 Int
  |  Clo11 Expr11
  deriving Show

subst11 :: String -> Expr11 -> Expr11 -> Expr11
subst11 x  s  (Lam11 y e)    |  x == y     = Lam11 y e
                             |  otherwise  = Lam11 y (subst11 x s e)
subst11 x  s  (Var11 y)      |  x == y     = s
                             |  otherwise  = Var11 y
subst11 x  s  (App11 e1 e2)  =  App11 (subst11 x s e1) (subst11 x s e2)
subst11 _  _  (Num11 z)      =  Num11 z
subst11 _  _  (Clo11 e)      =  Clo11 e
\end{code}
%endif
%
\begin{code}
normalize1 :: Expr11 -> Expr11
normalize1 (Lam11 x e)    = Lam11 x (gray (normalize1 e))
normalize1 (Var11 x)      = Var11 x
normalize1 (App11 e1 e2)  = case normalize1 e1 of
  Lam11 x e  -> normalize1 (subst11 x (Clo11 (normalize1 e2)) e)
  e1'        -> App11 e1' (normalize1 e2)
normalize1 (Num11 z)      = Num11 z
normalize1 (Clo11 e)      = e
\end{code}
%
Just like |interp1|, the |normalize1| function closes off terms before substituting.
However, because |normalize1| evaluates under $\lambda$ binders, closures may be prematurely unpacked, which may result in variable capture.
For example, say we apply $(\lambda x.\, \lambda y.\, x)$ to  the free variable $y$.
We would expect the result of evaluating this application to contain $y$ as a free variable.
However, using |normalize1|, the free variable $y$ is captured:
%
\begin{align*}
      &|normalize1|\ ((\lambda x.\, \lambda y.\, x)\ y)\\
|==|\ &|normalize1|\ (\lambda y.\, \lfloor y \rfloor)\\
|==|\ &\lambda y.\, \color{red}{|normalize1|\ \lfloor y \rfloor}\\
|==|\ &\lambda y.\, \color{red}{y}
\end{align*}
%
The next section discusses a more general substitution strategy due to Berkling~and~Fehr~\cite{berkling1982amodification} which does not have this limitation, which does not rename variables, and which is more efficient than the renaming based approach in \cref{sec:intermezzo} but less efficient than the renamingless substitution strategy discussed in~\cref{sec:interpreting-open}.
