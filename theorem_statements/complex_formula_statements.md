>The theorem statements below are adapted from https://artofproblemsolving.com/ and may not be identical. In particular, when a problem asks the reader to evaluate an expression, we instead equate that expression to X so that the problem can be formalised as that equality. All formulas render well in VSCode though some don't render well on GitHub. 


>Putnam 1940 B6

The determinant of the matrix 
$$\begin{pmatrix}
a_{1}^{2}+k & a_1 a_2 & a_1 a_3 &\ldots & a_1 a_n\\
a_2 a_1 & a_{2}^{2}+k & a_2 a_3 &\ldots & a_2 a_n\\
\ldots & \ldots & \ldots & \ldots & \ldots \\
a_n a_1& a_n a_2 & a_n a_3 & \ldots & a_{n}^{2}+k
\end{pmatrix}$$
is divisible by $k^{n-1}$.

>Putnam 1965 B1

Prove that $ \lim_{n\to\infty} \int_0^1 \int_0^1 \cdots \int_0^1 \cos ^ 2 \left\{\frac{\pi}{2n}(x_1+x_2+\cdots+x_n)\right\} dx_1dx_2\cdots dx_n.$

>Source not clear.

Let $a_1, a_2, \dots, a_n$ be real numbers such that $a_1+a_2+\cdots+a_n = 0$ and $a_1^2+a_2^2+\cdots+a_n^2 = 1$. Then the maximum possible value of $a_1a_2 + a_2a_3 + a_3a_4 + \cdots + a_na_1$ is $X$.

>Putnam 1952 A5

Let $a_j$ with $(j = 1, 2, \ldots, n)$ be entirely arbitrary numbers except that no one is equal to unity. Prove that $$ a_1 + \sum^n_{i=2} a_i \prod^{i-1}_{j=1} (1 - a_j) = 1 - \prod^n_{j=1} (1 - a_j).$$

>Putnam 2006 A6

Suppose that $f(x,y)$ is a continuous real-valued function on the unit square $0\le x\le1,0\le y\le1.$ Then

$\int_0^1\left(\int_0^1f(x,y)dx\right)^2dy + \int_0^1\left(\int_0^1f(x,y)dy\right)^2dx$

$\le\left(\int_0^1\int_0^1f(x,y)dxdy\right)^2 + \int_0^1\int_0^1\left[f(x,y)\right]^2dxdy.$


>Putnam 2013 A3

Suppose that the real numbers $a_0,a_1,\dots,a_n$ and $x,$ with $0<x<1,$ satisfy $$\frac{a_0}{1-x}+\frac{a_1}{1-x^2}+\cdots+\frac{a_n}{1-x^{n+1}}=0.$$ Prove that there exists a real number $y$ with $0<y<1$ such that $a_0+a_1y+\cdots+a_ny^n=0.$

>Putnam 1953 A6

The sequence
$$ \sqrt{7} , \sqrt{7-\sqrt{7}}, \sqrt{7-\sqrt{7-\sqrt{7}}}, \ldots$$
converges to $X$.

>Putnam 1956 A1

We have
$$ \lim_{x\to \infty} \left( \frac{a^x -1}{x(a-1)} \right)^{1/ x} = X,$$
where $a>0$ and $a\ne 1.

>Putnam 1958 A1

If $a_0 , a_1 ,\ldots, a_n$ are real number satisfying
$$ \frac{a_0 }{1} + \frac{a_1 }{2} + \ldots + \frac{a_n }{n+1}=0,$$
show that the equation $a_n x^n + \ldots +a_1 x+a_0 =0$ has at least one real root.

>Putnam 1958 A4

If $a_1 ,a_2 ,\ldots, a_n$ are complex numbers such that
$$ |a_1| =|a_2 | =\cdots = |a_n| =r \ne 0,$$
and if $T_s$ denotes the sum of all products of these $n$ numbers taken $s$ at a time, prove that
$$ \left| \frac{T_s }{T_{n-s}}\right| =r^{2s-n}$$
whenever the denominator of the left-hand side is different from $0$.

>Putnam 1992 B5

Let $D_n$ denote the value of the $(n -1) \times (n - 1)$ determinant
$$ \begin{pmatrix}
3 & 1 &1 & \ldots & 1\\
1 & 4 &1 & \ldots & 1\\
1 & 1 & 5 & \ldots & 1\\
\vdots & \vdots & \vdots &  \ddots & \vdots\\
1 & 1 & 1 & \ldots & n+1
\end{pmatrix}.$$
Then $\max \left\{ \frac{D_n }{n!} \, | \, n \geq 2\right\} = X$.


>Putnam 1974 B5

We have
$$1+\frac{n}{1!} + \frac{n^{2}}{2!} +\ldots+  \frac{n^{n}}{n!} > \frac{e^{n}}{2}$$
for every integer $n\geq 0.$

>Putnam 1951 A1

The determinant: $$ \begin{vmatrix} 0 & a & b & c \\ -a & 0 & d & e \\ -b & -d & 0 & f \\ -c & -e & -f & 0 \end{vmatrix} $$ is non-negative, if its elements $a, b, c,$ etc., are real.

>Putnam 1951 A7

If the series $a_1 + a_2 + a_3 + \cdots + a_n + \cdots$ converges, then the series $a_1 + a_2 / 2 + a_3 / 3 + \cdots + a_n / n + \cdots$ converges also.



>Putnam 1950 A2

The following series converges:
$$ \frac 1{\log (2!)} + \frac 1{\log (3!)} + \frac 1{\log (4!)} + \cdots + \frac 1{\log (n!)} +\cdots.$$

The following series diverges:
$$ \frac 13 + \frac 1{3\sqrt3} + \frac 1{3\sqrt3 \sqrt[3]3} + \cdots + \frac 1{3\sqrt3 \sqrt[3]3 \cdots \sqrt[n]3} + \cdots.$$


>Putnam 1970 B1

We have
$$\lim_{n\to \infty} \frac{1}{n^4 } \prod_{i=1}^{2n} (n^2 +i^2 )^{\frac{1}{n}} = X.$$

>Putnam 1949 A6

For every real or complex $x$ we have
$$\prod_{k=1}^{\infty} \frac{1+2\cos \frac{2x}{3^{k}}}{3} =\frac{\sin x}{x}.$$

>Putnam 1967 B6

If $f$ and $g$ are continuous and periodic functions with period $1$ on the real line, then
$$\lim_{n\to \infty} \int_{0}^{1} f(x)g (nx)\; dx =\left( \int_{0}^{1} f(x)\; dx\right)\left( \int_{0}^{1} g(x)\; dx\right).$$

>Putnam 1967 B6

Let $f$ be a real-valued function having partial derivatives and which is defined for $x^2 +y^2 \leq1$ and is such that $|f(x,y)|\leq 1.$ Show that there exists a point $(x_0, y_0 )$ in the interior of the unit circle such that
$$\left( \frac{ \partial f}{\partial x}(x_0 ,y_0 ) \right)^{2}+ \left( \frac{ \partial f}{\partial y}(x_0 ,y_0 ) \right)^{2} \leq 16.$$

>Putnam 2017 B4
We have
$$\sum_{k=0}^{\infty}\left(3\cdot\frac{\ln(4k+2)}{4k+2}-\frac{\ln(4k+3)}{4k+3}-\frac{\ln(4k+4)}{4k+4}-\frac{\ln(4k+5)}{4k+5}\right) = X.$$
(As usual, $\ln x$ denotes the natural logarithm of $x.$)


>Putnam 2010 B1

There does not exist an infinite sequence of real numbers $a_1,a_2,a_3,\dots$ such that
$$a_1^m+a_2^m+a_3^m+\cdots=m$$
for every positive integer $m$.



>Putnam 2002 B6

Let $p$ be a prime number. Prove that the determinant of the matrix 
$$
 \begin{bmatrix}x & y & z\\ x^p & y^p & z^p \\ x^{p^2} & y^{p^2} & z^{p^2} \end{bmatrix}
 $$
   is congruent modulo $p$ to a product of polynomials of the form $ax+by+cz$, where $a$, $b$, and $c$ are integers. (We say two integer polynomials are congruent modulo $p$ if corresponding coefficients are congruent modulo $p$.)


>Putnam 1958 A1

If $a_0 , a_1 ,\ldots, a_n$ are real number satisfying
$$ \frac{a_0 }{1} + \frac{a_1 }{2} + \ldots + \frac{a_n }{n+1}=0,$$
then the equation $a_n x^n + \ldots +a_1 x+a_0 =0$ has at least one real root.

>Putnam 1953 B7

Let $w\in (0,1)$ be an irrational number. Prove that $w$ has a unique convergent expansion of the form
$$w= \frac{1}{p_0} - \frac{1}{p_0 p_1 } + \frac{1}{ p_0 p_1 p_2 } - \frac{1}{p_0 p_1 p_2 p_3 } +\ldots,$$
where $1\leq p_0 < p_1 < p_2 <\ldots $ are integers. If $w= \frac{1}{\sqrt{2}},$ then $p_0 = X_0$ , $p_1 = X_1$ , $p_2 = X_2$.


>Putnam 1953 A1

For every positive integer $n$ it holds that
$$ \frac{2}{3} n \sqrt{n} < \sqrt{1} + \sqrt{2} +\ldots +\sqrt{n} < \frac{4n+3}{6} \sqrt{n}.$$


>Putnam 2000 B2

The expression $$\dfrac {\text {gcd}(m, n)}{n} \dbinom {n}{m} $$ is an integer for all pairs of integers $ n \ge m \ge 1 $.

>Putnam 1957 B3

For $f(x)$ a positive, monotone decreasing function defined in $[0,1]$. Then  
$$ \int_{0}^{1} f(x) dx \cdot \int_{0}^{1} xf(x)^{2} dx \leq \int_{0}^{1} f(x)^{2} dx \cdot \int_{0}^{1} xf(x) dx.$$


>Putnam 1973 B4

 On $[0, 1]$, let $f(x)$ have a continuous derivative satisfying $0 <f'(x) \leq1$. Also suppose that $f(0) = 0.$ Then
$$ \left( \int_{0}^{1} f(x)\; dx \right)^{2} \geq \int_{0}^{1} f(x)^{3}\; dx.$$
Moreover there exists an $f$ for which equality occurs.


>Putnam 1960 A3

If $t_1 , t_2, t_3, t_4, t_5$ are real numbers, then
$$\sum_{j=1}^{5} (1-t_j )\exp \left( \sum_{k=1}^{j} t_k \right) \leq e^{e^{e^{e}}}.$$


>Putnam 1960 B2

We have double series
$$\sum_{j=0}^{\infty} \sum_{k=0}^{\infty} 2^{-3k -j -(k+j)^{2}} = X$$



>Putnam 1960 B5

Define a sequence $(a_n)$ by $a_0 =0$ and $a_n = 1 +\sin(a_{n-1}-1)$ for $n\geq 1$. Then
$$\lim_{n\to \infty} \frac{1}{n} \sum_{k=1}^{n} a_k = X.$$

>Putnam 1961 B4

Let $x_1 , x_2 ,\ldots, x_n$ be real numbers in $[0,1].$ Then the maximum value of the sum of the $\frac{n(n-1)}{2}$ terms:
$$\sum_{i<j}|x_i -x_j | = X.$$


>Putnam 1961 B1

Let $a_1 , a_2 , a_3 ,\ldots$ be a sequence of positive real numbers, define $s_n = \frac{a_1 +a_2 +\ldots+a_n }{n}$ and $r_n = \frac{a_{1}^{-1} +a_{2}^{-1} +\ldots+a_{n}^{-1} }{n}.$ If  $\lim_{n\to \infty} s_n $ and $\lim_{n\to \infty} r_n $ exist, then the product of these limits is not less than $1.$


>Putnam 1961 B5

Let $k$ be a positive integer, and $n$ a positive integer greater than $2$. Define 
$$f_{1}(n)=n,\;\; f_{2}(n)=n^{f_{1}(n)},\;\ldots\;, f_{j+1}(n)=n^{f_{j}(n)}.$$
Then the following inequalities hold 
$$f_{k}(n) < n!! \cdots ! < f_{k+1}(n),$$
where the middle term has $k$ factorial symbols.

>Putnam 1959 B7

For each positive integer $n$, let $f_n$ be a real-valued symmetric function of $n$ real variables. Suppose that for  all $n$ and all real numbers $x_1,\ldots,x_n, x_{n+1},y$ it is true that

 $\;(1)\; f_{n}(x_1 +y ,\ldots, x_n +y) = f_{n}(x_1 ,\ldots, x_n) +y,$
 $\;(2)\;f_{n}(-x_1 ,\ldots, -x_n) =-f_{n}(x_1 ,\ldots, x_n),$
 $\;(3)\; f_{n+1}(f_{n}(x_1,\ldots, x_n),\ldots, f_{n}(x_1,\ldots, x_n), x_{n+1}) =f_{n+1}(x_1 ,\ldots, x_{n}).$

Then $f_{n}(x_{1},\ldots, x_n) =\frac{x_{1}+\cdots +x_{n}}{n}.$

>Putnam 1952 B3

Show that the necessary and sufficient conditions that the equation $$ \begin{vmatrix} 0 & a_1 - x & a_2 - x \\ -a_1 - x & 0 & a_3 - x \\ -a_2 - x & -a_3 - x & 0\end{vmatrix} = 0 \qquad (a_i \neq 0) $$ has a multiple root if and only if $a_3a_1-a_1a_2-a_2a_3=0$.

>Putnam 1950 A6

Each coefficient $a_n$ of the power series 
$$
a_0 + a_1 x + a_2 x^2 + a_3 x^3 + \cdots = f(x)
$$ 
has either the value of $1$ or the value $0.$ 
Then, if $f(0.5)$ is a rational number, $f(x)$ is a rational function.


>Putnam 1952 A1

Let 
$$ f(x) = \sum_{i=0}^{i=n} a_i x^{n - i}
$$
be a polynomial of degree $n$ with integral coefficients. If $a_0, a_n,$ and $f(1)$ are odd, then $f(x) = 0$ has no rational roots.


>Putnam 1962 B1

Let $x^{(n)}=x(x-1)\cdots (x-n+1)$ for $n$ a positive integer and let $x^{(0)}=1.$ Prove that
$$(x+y)^{(n)}= \sum_{k=0}^{n} \binom{n}{k} x^{(k)} y^{(n-k)}.$$

>Putnam 2020 A2

Let $k$ be a nonnegative integer. Then
$$ \sum_{j=0}^k 2^{k-j} \binom{k+j}{j} =X. $$

>Putnam 1970 A4

Let a sequence $(x_n )$ be such that $\lim_{n\to \infty} x_n - x_{n-2}=0.$ Then 
$$\lim_{n\to \infty} \frac{x_n -x_{n-1}}{n}=0.$$



>Putnam 2007 B5

Let $ k$ be a positive integer. Prove that there exist polynomials $ P_0(n),P_1(n),\dots,P_{k-1}(n)$ (which may depend on $ k$) such that for any integer $ n,$
$$
\left\lfloor\frac{n}{k}\right\rfloor^k=P_0(n)+P_1(n)\left\lfloor\frac{n}{k}\right\rfloor +\cdots+ 
P_{k-1}(n)\left\lfloor\frac{n}{k}\right\rfloor^{k-1}.
$$
($ \lfloor a\rfloor$ means the largest integer $ \le a.$

>Putnam 1947 B2

Let $f(x)$ be a differentiable function defined on the interval $(0,1)$ such that $|f'(x)| \leq M$ for $0<x<1$ and a positive real number $M.$ Then
$$\left| \int_{0}^{1} f(x)\; dx - \frac{1}{n} \sum_{k=1}^{n} f\left(\frac{k}{n} \right) \right | \leq \frac{M}{n}.$$


>Putnam 1980 B6

An infinite array of rational numbers $G(d, n)$ is defined for integers $d$ and $ n$ with $1\leq d \leq n$ as follows:
$$G(1, n)= \frac{1}{n}, \;\;\; G(d,n)= \frac{d}{n} \sum_{i=d}^{n} G(d-1, i-1) \; \text{for} \; d>1.$$
For $1 < d < p$ and $p$ prime, then $G(d, p)$ is expressible as a quotient $s/ t$  of integers $s$ and $t$ with $t$ not divisible by $p.$

>Putnam 1949 B4 

The coefficients $a_1 , a_2 , a_3 ,\ldots$ in the expansion
$$\frac{1}{4}\left(1+x-\frac{1}{\sqrt{1-6x+x^{2}}}\right) =a_{1} x+ a_2 x^2 + a_3 x^3 +\ldots$$
are positive integers.

>Putnam 1948 A5

Let $\xi_1,\ldots,\xi_n$ denote the $n$-th roots of unity, then
$$\prod_{1\leq i<j \leq n} (\xi_{i}-\xi_j )^2 = X.$$

>Putnam 1999 A1

There exist polynomials $f(x)$, $g(x)$, and $h(x)$, such that for all $x$, 
$$
|f(x)|-|g(x)|+h(x)=\begin{cases}-1 & \text{if }x<-1\\3x+2 &\text{if }-1\leq x\leq 0\\-2x+2 & \text{if }x>0.\end{cases}
$$

>Putnam 1998 A3

Let $f$ be a real function on the real line with continuous third derivative. Then there exists a point $a$ such that $$f(a)\cdot f^\prime(a)\cdot f^{\prime\prime}(a)\cdot f^{\prime\prime\prime}(a)\geq 0.$$


>Putnam 1964 A5

There exists a constant $K$ such that the following inequality holds for any sequence of positive numbers $a_1 , a_2 , a_3 , \ldots:$
$$\sum_{n=1}^{\infty} \frac{n}{a_1 + a_2 +\ldots + a_n } \leq K \sum_{n=1}^{\infty} \frac{1}{a_{n}}.$$


>Putnam 1964 A4

Let $p_n$ be a bounded sequence of integers which satisfies the recursion
$$p_n =\frac{p_{n-1} +p_{n-2} + p_{n-3}p _{n-4}}{p_{n-1} p_{n-2}+ p_{n-3} +p_{n-4}}.$$
Then sequence $p_n$ eventually becomes periodic.


>Putnam 1975 B3

Let $n$ be a positive integer. Let $S=\{a_1,\ldots, a_{k}\}$ be a finite collection of at least $n$ not necessarily distinct positive real numbers. Let 
$$
f(S)=\left(\sum_{i=1}^{k} a_{i}\right)^{n}
$$ and 

$$
g(S)=\sum_{1\leq i_{1}<\ldots<i_{n} \leq  k} a_{i_{1}}\cdot\ldots\cdot a_{i_{n}}.
$$ 
Then $\sup_{S} \frac{g(S)}{f(S)} = X$.

>Putnam 1972 A6

Let $f$ be an integrable real-valued function on the closed interval $ [0, 1]$ such that
$$\int_{0}^{1} x^{m}f(x) dx=\begin{cases} 0 \;\; \text{for}\; m=0,1,\ldots,n-1;\\
1\;\; \text{for}\; m=n. \end{cases} $$
Then $|f(x)|\geq2^{n}(n+1)$ on a set of positive measure.

>Putnam 1978 A2

Let $a,b, p_1 ,p_2, \ldots, p_n$ be real numbers with $a \ne b$. Define $f(x)= (p_1 -x) (p_2 -x) \cdots (p_n -x)$. Then we have
$$ \text{det} \begin{pmatrix} p_1 & a& a & \cdots & a \\
b & p_2 & a & \cdots & a\\
b & b & p_3 & \cdots & a\\
\vdots & \vdots & \vdots & \ddots & \vdots\\
b & b& b &\cdots &p_n
\end{pmatrix}= \frac{bf(a) -af(b)}{b-a}.$$

>Putnam 1981 A3

We have
$$ \lim_{t\to \infty} e^{-t} \int_{0}^{t} \int_{0}^{t} \frac{e^x -e^y }{x-y} \,dx\,dy = X.$$


>Putnam 1941 A2

The $n$-th derivative with respect to $x$ of
$$
\int_{0}^{x} \left(1+\frac{x-t}{1!}+\frac{(x-t)^{2}}{2!}+\ldots+\frac{(x-t)^{n-1}}{(n-1)!}\right)e^{nt} dt
$$ 
is equal to $X$.

>Putnam 1949 B5

let $(a_{n})$ be an arbitrary sequence of positive numbers. Then
$$\limsup_{n\to \infty} \left(\frac{a_1 +a_{n+1}}{a_{n}}\right)^{n} \geq e.$$

>Putnam 2021 B2

Show that the maximum value of the sum
$$
S=\sum_{n=1}^{\infty}\frac{n}{2^n}(a_1 a_2 \dots a_n)^{\frac{1}{n}}
$$
over all sequences $a_1,a_2,a_3,\dots$ of nonnegative real numbers satisfying
$$
\sum_{k=1}^{\infty}a_k=1
$$
equals $X$.


