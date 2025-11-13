
\section{Mathematical Perspective}
Wightman and others have questioned for approximately fifty years whether
mathematically well-defined examples of relativistic, nonlinear quantum field the-
ories exist. We now have a partial answer: Extensive results on the existence and
physical properties of nonlinear QFTs have been proved through the emergence of
the body of work known as ``constructive quantum field theory'' (CQFT).

The answers are partial, for in most of these field theories one replaces the
Minkowski space-time \(M_4\) by a lower-dimensional space-time \(M_2\) or \(M_3\), or by a
compact approximation such as a torus. (Equivalently in the Euclidean formulation
one replaces Euclidean space-time \(\mathbb{R}^4\) by \(\mathbb{R}^2\) or \(\mathbb{R}^3\).) Some results are known for
Yang--Mills theory on a 4-torus \(T_4\) approximating \(\mathbb{R}^4\), and, while the construction
is not complete, there is ample indication that known methods could be extended
to construct Yang--Mills theory on \(T_4\).

In fact, at present we do not know any non-trivial relativistic field theory that
satisfies the Wightman (or any other reasonable) axioms in four dimensions. So even
having a detailed mathematical construction of Yang--Mills theory on a compact
space would represent a major breakthrough. Yet, even if this were accomplished,
no present ideas point the direction to establish the existence of a mass gap that is
uniform in the volume. Nor do present methods suggest how to obtain the existence
of the infinite volume limit \(T_4 \to \mathbb{R}^4\).

\subsection{Methods}
Since the inception of quantum field theory, two central methods
have emerged to show the existence of quantum fields on non-compact configuration
space (such as Minkowski space). These known methods are:

\begin{itemize}
    \item[(i)] Find an exact solution in closed form;
    \item[(ii)] Solve a sequence of approximate problems, and establish convergence of
    these solutions to the desired limit.
\end{itemize}

Exact solutions may be available for nonlinear fields for special values of the coupling
which yields extra symmetries or integrable models. They might be achieved
after clever changes of variables. In the case of four-dimensional Yang--Mills theory,
an exact solution appears unlikely, though there might some day be an asymptotic
solution in a large \(N\) limit.

The second method is to use mathematical approximations to show the convergence
of approximate solutions to exact solutions of the nonlinear problems,
known as constructive quantum field theory, or CQFT. Two principal approaches—
studying quantum theory on Hilbert space, and studying classical functional integrals—
are related by the Osterwalder--Schrader construction. Establishing uniform
a priori estimates is central to CQFT, and three schemes for establishing estimates
are:

\begin{itemize}
    \item[(a)] correlation inequalities,
    \item[(b)] symmetries of the interaction,
    \item[(c)] convergent expansions.
\end{itemize}

The correlation inequality methods have an advantage; they are general. But correlation
inequalities rely on special properties of the interaction that often apply
only for scalar bosons or abelian gauge theories. The use of symmetry also applies
only to special values of the couplings and is generally combined with another
method to obtain analytic control. In most known examples, perturbation series,
i.e., power series in the coupling constant, are divergent expansions; even Borel and
other resummation methods have limited applicability.

This led to development of expansion methods, generally known as cluster expansions.
Each term in a cluster expansion sum depends on the coupling constants
in a complicated fashion; they often arise as functional integrals. One requires
sufficient quantitative knowledge of the properties of each term in an expansion to
ensure the convergence of the sum and to establish its qualitative properties. Refined
estimates yield the rate of exponential decay of Green’s functions, magnitude
of masses, the existence of symmetry breaking (or its preservation), etc.

Over the past thirty years, a panoply of expansion methods have emerged as a
central tool for establishing mathematical results in CQFT. In their various incarnations,
these expansions encapsulate ideas of the asymptotic nature of perturbation
theory, of space-time localization, of phase-space localization, of renormalization
theory, of semi-classical approximations (including ``non-perturbative'' effects), and
of symmetry breaking. One can find an introduction to many of these methods and
references in~\cite{18}, and a more recent review of results in~\cite{28}. These expansion methods
can be complicated and the literature is huge, so we can only hope to introduce
the reader to a few ideas; we apologize in advance for important omissions.

\subsection{The First Examples: Scalar Fields}
Since the 1940s the quantum Klein--Gordon field \(\phi\) provided an example of a linear, scalar, mass-\(m\) field theory (arising
from a quadratic potential). This field, and the related free spinor Dirac field,
served as models for formulating the first axiom schemes in the 1950s~\cite{45}.

Moments of a Euclidean-invariant,
reflection-positive, ergodic, Borel measure
\(d\mu\) on the space \(\mathcal{S}'(\mathbb{R}^d)\) of tempered distributions may satisfy the Osterwalder--
Schrader axioms. The Gaussian measure \(d\mu\) with mean zero and covariance \(C =
(-\Delta + m_0^2)^{-1}\) yields the free, mass-\(m_0\) field; but one requires non-Gaussian \(d\mu\) to
obtain nonlinear fields. (For the Gaussian measure, reflection positivity is equivalent
to positivity of the transformation \(\Theta_C\), restricted to \(L^2(\mathbb{R}^{d+}_+) \subset L^2(\mathbb{R}^d)\). Here
\(\Theta : t \to -t\) denotes the time-reflection operator, and \(\mathbb{R}^{d+}_+ = \{(t, \vec{x}) : t \geq 0\}\) is the
positive-time subspace.)

The first proof that nonlinear fields satisfy the Wightman axioms and the first
construction of such non-Gaussian measures only emerged in the 1970s. The initial
examples comprised fields with small, polynomial nonlinearities on \(\mathbb{R}^2\): first in
finite volume, and then in the infinite volume limit~\cite{15,19,22}. These
field theories
obey the Wightman axioms (as well as all other axiomatic formulations), the fields
describe particles of a definite mass, and the fields produce multi-particle states
with non-trivial scattering~\cite{19}. The scattering matrix can be expanded as an
asymptotic series in the coupling constants, and the results agree term-by-term
with the standard description of scattering in perturbation theory that one finds in
physics texts~\cite{37}.

A quartic Wightman QFT on \(\mathbb{R}^3\) also exists, obtained by constructing a remarkable
non-Gaussian measure \(d\mu\) on \(\mathcal{S}'(\mathbb{R}^3)\)~\cite{16,10}. This merits further study.

We now focus on some properties of the simplest perturbation to the action-
density of the free field, namely, the even quartic polynomial
\begin{equation}
    \frac{1}{2} \lambda \phi^4 + \sigma \phi^2 + c.
\end{equation}
The coefficients \(0 < \lambda\) and \(\sigma, c \in \mathbb{R}\) are real parameters, all zero for the free field.
For \(0 < \lambda \ll 1\), one can choose \(\sigma(\lambda), c(\lambda)\) so the field theory described by (3) exists,
is unique, and has a mass equal to \(m\) such that \(|m - m_0|\) is small.

Because of the local singularity of the nonlinear field, one must first cut off the
interaction. The simplest
method is to truncate the Fourier expansion of the field
\(\phi\) in (3) to \(\phi_\kappa(x) = \int_{|k| \leq \kappa} \tilde{\phi}(k) e^{-ikx} dk\) and to compactify the spatial volume of
the perturbation to \(V\). One obtains the desired quantum field theory as a limit
of the truncated approximations. The constants \(\sigma, c\) have the form \(\sigma = \alpha \lambda + \beta \lambda^2\)
and \(c = \gamma \lambda + \delta \lambda^2 + \cdots \lambda^3\). One desires that the expectations of products of fields
have a limit as \(\kappa \to \infty\). One chooses \(\alpha, \gamma\) (in dimension 2), and one chooses all the
coefficients \(\alpha, \beta, \gamma, \delta, \cdots\) (in dimension 3), to depend on \(\kappa\) in the way that perturbation
theory suggests. One then proves that the expectations converge as \(\kappa \to \infty\), even
though the specified constants \(\alpha, \ldots\) diverge. These constants provide the required
renormalization of the interaction. In the three-dimensional case one also needs to
normalize vectors in the Fock space by a constant that diverges with \(\kappa\); one calls this
constant a wave-function renormalization constant.

The ``mass'' operator in natural units is \(M = \sqrt{H^2 - \vec{P}^2} \geq 0\), and the vacuum
vector \(\Omega\) is a null vector, \(M \Omega = 0\). Massive single particle states are eigenvectors of
an eigenvalue \(m > 0\). If \(m\) is an isolated eigenvalue of \(M\), then one infers from the
Wightman axioms and Haag--Ruelle scattering theory that asymptotic scattering
states of an arbitrary number of particles exist, see~\cite{24,18}.

The fundamental problem of asymptotic completeness is the question whether
these asymptotic states (including possible bound states) span \(\mathcal{H}\). Over the past
thirty years, several new methods have emerged, yielding proofs of asymptotic completeness
in scattering theory for non-relativistic quantum mechanics. This gives
some hope that one can now attack the open problem of asymptotic completeness
for any known example of nonlinear quantum field theory.

In contrast to the existence of quantum fields with a \(\phi^4\) nonlinearity in dimensions
2 and 3, the question of extending these results to four dimensions is problematic.
It is known that self-interacting scalar fields with a quartic nonlinearity do
not exist in dimension 5 or greater~\cite{12,1}. (The proofs apply to field theories with
a single, scalar field.) Analysis of the borderline dimension 4 (between existence
and non-existence) is more subtle; if one makes some reasonable (but not entirely
proved) assumptions, one also can conclude triviality for the quartic coupling in four
dimensions. Not only is this persuasive evidence, but furthermore the quartic coupling
does not have the property of asymptotic freedom in four dimensions. Thus
all insights from random walks, perturbation theory, and renormalization analysis
point toward triviality of the quartic interaction in four dimensions.

Other polynomial interactions in four dimensions are even more troublesome:
The classical energy of the cubic interaction is unbounded from below, so it appears
an unlikely candidate for a quantum theory where positivity of the energy
is an axiom. And polynomial interactions of degree greater than quartic are more
singular in perturbation theory than the quartic interaction.

All these reasons complement the physical and geometric importance of Yang--
Mills theory and highlight it as the natural candidate for four-dimensional CQFT.

\subsection{Large Coupling Constant}
In two dimensions, the field theory with energy
density (3) exists for all positive \(\lambda\). For \(0 \leq \lambda \ll 1\) the solution is unique under a
variety of conditions; but for \(\lambda \gg 1\) two different solutions exist, each characterized
by its ground state or ``phase.'' The solution in each phase satisfies the Osterwalder--
Schrader and Wightman axioms with a non-zero mass gap and a unique, Poincaré-
invariant vacuum state. The distinct solutions appear as a bifurcation of a unique
approximating solution with finite volume \(V\) as \(V \to \infty\).

One exhibits this behavior by reordering and scaling the \(\lambda \phi^4\) interaction (3) with
\(\lambda \gg 1\) to obtain an equivalent double-well potential of the form
\begin{equation}
    \frac{1}{2} \lambda (\phi^2 - 1)^2 + \sigma \phi^2 + c.
\end{equation}
Here \(\lambda \ll 1\) is a new coupling constant and the renormalization constants \(\sigma\) and
\(c\) are somewhat different from those above. The two solutions for a given \(\lambda\) are
related by the broken \(\phi \to -\phi\) symmetry of the interaction (4). The proof of these
facts relies upon developing a convergent cluster expansion about each minimum
of the potential arising from (4) and proving the probability of tunneling between
the two solutions is small~\cite{20}.

A critical value \(\lambda_c\) of \(\lambda\) in (3) provides a boundary between the uniqueness of the
solution (for \(\lambda < \lambda_c\)) and the existence of a phase transition \(\lambda > \lambda_c\). As \(\lambda\) increases
to \(\lambda_c\), the mass gap \(m = m(\lambda)\) decreases monotonically and continuously to zero
~\cite{23,17,32}.

The detailed behavior of the field theory (or the mass) in the neighborhood of
\(\lambda = \lambda_c\) is extraordinarily difficult to analyze; practically nothing has been proved.
Physicists have a qualitative picture based on the assumed fractional power-law
\(\nu\)
behavior \(m(\lambda) \sim |\lambda_c - \lambda|^\nu\) above or below the critical point, where the exponent
\(\nu\) depends on the dimension. One also expects that the critical coupling \(\lambda_c\) corresponds
to the greatest physical force between particles, and that these critical
theories are close to scaling limits of Ising-type modes in statistical physics. One
expects that further understanding of these ideas will result in new computational
tools for quantum fields and for statistical physics.

There is some partial understanding of a more general multi-phase case. One
can find an arbitrary number \(n\) of phases by making a good choice of a polynomial
energy density \(P_n(\phi)\) with \(n\) minima. It is interesting to study the perturbation
of a fixed such polynomial \(P_n\) by polynomials \(Q\) of lower degree and with small
coefficients. Among these perturbations one can find families of polynomials \(Q(\phi)\)
that yield field theories with exactly \(n' \leq n\) phases~\cite{26}.

\subsection{Yukawa Interactions and Abelian Gauge Theory}
The existence of bo-
son-fermion interactions is also known in two dimensions, and partial results exist
in three dimensions. In two dimensions Yukawa interactions of the form \(\bar{\psi}\psi\phi\)
exist with appropriate renormalization, as well as their generalizations of the form
\(P(\phi) + \bar{\psi}\psi Q''(\phi)\), see~\cite{42,18}. The supersymmetric case \(P = |Q'|^2\) requires extra
care in dealing with cancellations of divergences, see~\cite{28} for references.

A continuum two-dimensional Higgs model describes an abelian gauge field interacting
with a charged scalar field. Brydges, Fröhlich, and Seiler constructed this
theory and showed that it satisfies the Osterwalder--Schrader axioms~\cite{7}, providing
the only complete example of an interacting gauge theory satisfying the axioms. A
mass gap exists in this model~\cite{4}. Extending all these conclusions to a non-abelian
Higgs model, even in two dimensions, would represent a qualitative advance.

Partial results on the three-dimensional \(\bar{\psi}\psi\phi\) interaction have been established,
see~\cite{30}, as well as for other more singular interactions~\cite{14}.
