# A barrier for scalar reweighting of the two ternary roots

In the full first orbit, one might give adjustable weights $\lambda,1-\lambda$ to ternary roots 1 and 2 after removing the pure ternary tower. An exponent-one cylinder with the largest probability can sit in a different root from the deepest cylinders with the largest probability. The following fixed-schedule obstruction continues to hold when that incompatibility is retained exactly for each phase.

Consider the *scalar* relaxation which charges the mixed smooth labels by the sum of their individual conditional cylinder bounds, pricing the forced 15-class in its actual root. Price each rough stage by the uncoupled positive-part comparison with the schedule named `SCHEDULE` in joint_savings.py. For the finite pure-head geometry below, the sum of these upper estimates, even maximized over just two possible assignments of the rough ternary phases, is **at least 1.03211827785959 for every root weight**. This is a lower bound on a proposed proof budget. It makes no assertion that a system covers positive density of any specific size or that the joint-stage method has this limitation.

Use height $h=6$ and the pure classes $0\bmod3$, $1\bmod9$, and $4+3^{a-1}\bmod3^a$ for $3\le a\le h$. On the 5-coordinate use $0\bmod5$ and $2+5^{b-1}\bmod5^b$ for $2\le b\le h$. These classes are disjoint within each coordinate. Normalize the uniform law separately in the remaining part of each ternary root, giving roots 1 and 2 weights $\lambda$ and $1-\lambda$. Write $U=\sum_{a=1}^h3^{-a}$, $V=\sum_{b=1}^h5^{-b}$ and $g_5=(1-V)^{-1}$. Before normalization, the surviving masses of the two roots are $s_1=2/3-U$ and $s_2=1/3$. All projections of depths at least two can simultaneously use the untouched ternary cylinder $7\bmod9$ within the first root, or an untouched cylinder of depth two in the second. The quinary tower leaves its root 1 untouched. The individual mixed-head price in this relaxation is
$$
C(\lambda)=g_5\!\left[
  \max\!\left\{\lambda/s_1,(1-\lambda)/s_2\right\}(U-1/3)V
  +\lambda/5+\max\{\lambda,1-\lambda\}(V-1/5)\right].
$$

For all rough classes with positive ternary exponent, choose their ternary phases nested in the first root, or choose them all nested in the second. Inside root $j$ a compatible depth-one cylinder has probability 1, and compatible cylinders of depth $e\ge2$ have probability $3^{-e}/s_j$. These two saturations suffice for the lower bound. For $1\le d\le h+1$ define $\Delta_d$ as the scalar price of starting with $d$ ternary divisors minus that of starting with $d-1$. Computing a finite lower bound for each $\Delta_d$ uses the nonnegative, increasing function
$$
(dR-t)_+-((d-1)R-t)_+.
$$
Here $R$ contains the quinary comparison factor and the preceding rough factors; the scalar stage multiplies the result by $c_p/(p-1)$. Use the appropriate finite quinary exponent law at height six, retain the rough primes from 11 to 8,009, clip each rough multiplicative factor at four and the accumulated product at 1,024. Componentwise downward rounding gives lower bounds $L_d\le\Delta_d$. Put $J=\sum_{e=2}^h3^{-e}L_{e+1}$ and $I_j=L_2+J/s_j$. The cost is at least
$$
C(\lambda)+L_1+\max\{\lambda I_1,(1-\lambda)I_2\}.
$$
Each of the maxima in this piecewise-affine lower bound has a single breakpoint. Checking $0,1,1/2,s_1/(s_1+s_2)$ and $I_2/(I_1+I_2)$ gives the stated bound. No estimate for later primes is required for this lower certificate because their prices are nonnegative. A different smooth-head charge, a different schedule, multi-stage distortion, or a nonproduct head law requires a new analysis.

    python3 root_weight_barrier.py

[Exact output and minimizing weight](root_weight_barrier.txt)
