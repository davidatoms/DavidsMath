1. The Physics of Gauge Theory
Since the early part of the 20th century, it has been understood that the descrip-
tion of nature at the subatomic scale requires quantum mechanics. In quantum me-
chanics, the position and velocity of a particle are noncommuting operators acting
on a Hilbert space, and classical notions such as “the trajectory of a particle” do
not apply.
But quantum mechanics of particles is not the whole story. In 19th and early
20th century physics, many aspects of nature were described in terms of ﬁelds—the
electric and magnetic ﬁelds that enter in Maxwell’s equations, and the gravitational
ﬁeld governed by Einstein’s equations. Since ﬁelds interact with particles, it be-
came clear by the late 1920s that an internally coherent account of nature must
incorporate quantum concepts for ﬁelds as well as for particles.
After doing this, quantities such as the components of the electric ﬁeld at diﬀer-
ent points in space-time become non-commuting operators. When one attempts to
construct a Hilbert space on which these operators act, one ﬁnds many surprises.
The distinction between ﬁelds and particles breaks down, since the Hilbert space
of a quantum ﬁeld is constructed in terms of particle-like excitations. Conventional
particles, such as electrons, are reinterpreted as states of the quantized ﬁeld. In
the process, one ﬁnds the prediction of “antimatter”; for every particle, there must
be a corresponding antiparticle, with the same mass and opposite electric charge.
Soon after P.A.M. Dirac predicted this on the basis of quantum ﬁeld theory, the
“positron” or oppositely charged antiparticle of the electron was discovered in cos-
mic rays.
The most important Quantum Field Theories (QFTs) for describing elementary
particle physics are gauge theories. The classical example of a gauge theory is
Maxwell’s theory of electromagnetism. For electromagnetism the gauge symmetry
group is the abelian group U (1). If A denotes the U (1) gauge connection, locally
a one-form on space-time, then the curvature or electromagnetic ﬁeld tensor is the
two-form F = dA, and Maxwell’s equations in the absence of charges and currents
read 0 = dF = d ∗ F . Here ∗ denotes the Hodge duality operator; indeed, Hodge
introduced his celebrated theory of harmonic forms as a generalization of the solu-
tions to Maxwell’s equations. Maxwell’s equations describe large-scale electric and
magnetic ﬁelds and also—as Maxwell discovered—the propagation of light waves,
at a characteristic velocity, the speed of light.
The idea of a gauge theory evolved from the work of Hermann Weyl. One can
ﬁnd in [34] an interesting discussion of the history of gauge symmetry and the
discovery of Yang–Mills theory [50], also known as “non-abelian gauge theory.”
At the classical level one replaces the gauge group U (1) of electromagnetism by a
compact gauge group G. The deﬁnition of the curvature arising from the connection
12
ARTHUR JAFFE AND EDWARD WITTEN
must be modiﬁed to F = dA + A ∧ A, and Maxwell’s equations are replaced by
the Yang–Mills equations, 0 = dA F = dA ∗ F , where dA is the gauge-covariant
extension of the exterior derivative.
These classical equations can be derived as variational equations from the Yang–
Mills Lagrangian
(1)
L=
1
4g 2
∫
Tr F ∧ ∗F,
where Tr denotes an invariant quadratic form on the Lie algebra of G. The Yang–
Mills equations are nonlinear—in contrast to the Maxwell equations. Like the
Einstein equations for the gravitational ﬁeld, only a few exact solutions of the
classical equation are known. But the Yang–Mills equations have certain properties
in common with the Maxwell equations: In particular they provide the classical
description of massless waves that travel at the speed of light.
By the 1950s, when Yang–Mills theory was discovered, it was already known that
the quantum version of Maxwell theory—known as Quantum Electrodynamics or
QED—gives an extremely accurate account of electromagnetic ﬁelds and forces. In
fact, QED improved the accuracy for certain earlier quantum theory predictions by
several orders of magnitude, as well as predicting new splittings of energy levels.
So it was natural to inquire whether non-abelian gauge theory described other
forces in nature, notably the weak force (responsible among other things for certain
forms of radioactivity) and the strong or nuclear force (responsible among other
things for the binding of protons and neutrons into nuclei). The massless nature
of classical Yang–Mills waves was a serious obstacle to applying Yang–Mills theory
to the other forces, for the weak and nuclear forces are short range and many of
the particles are massive. Hence these phenomena did not appear to be associated
with long-range ﬁelds describing massless particles.
In the 1960s and 1970s, physicists overcame these obstacles to the physical in-
terpretation of non-abelian gauge theory. In the case of the weak force, this was
accomplished by the Glashow–Salam–Weinberg electroweak theory [47, 40] with
gauge group H = SU (2) × U (1). By elaborating the theory with an additional
“Higgs ﬁeld,” one avoided the massless nature of classical Yang–Mills waves. The
Higgs ﬁeld transforms in a two-dimensional representation of H; its non-zero and
approximately constant value in the vacuum state reduces the structure group from
H to a U (1) subgroup (diagonally embedded in SU (2) × U (1)). This theory de-
scribes both the electromagnetic and weak forces, in a more or less uniﬁed way;
because of the reduction of the structure group to U (1), the long-range ﬁelds are
those of electromagnetism only, in accord with what we see in nature.
The solution to the problem of massless Yang–Mills ﬁelds for the strong in-
teractions has a completely diﬀerent nature. That solution did not come from
adding ﬁelds to Yang–Mills theory, but by discovering a remarkable property of the
quantum Yang–Mills theory itself, that is, of the quantum theory whose classical
Lagrangian has been given in (1). This property is called “asymptotic freedom”
[21, 38]. Roughly this means that at short distances the ﬁeld displays quantum
behavior very similar to its classical behavior; yet at long distances the classical
theory is no longer a good guide to the quantum behavior of the ﬁeld.
Asymptotic freedom, together with other experimental and theoretical discov-
eries made in the 1960s and 1970s, made it possible to describe the nuclear forceQUANTUM YANG–MILLS THEORY
3
by a non-abelian gauge theory in which the gauge group is G = SU (3). The ad-
ditional ﬁelds describe, at the classical level, “quarks,” which are spin 1/2 objects
somewhat analogous to the electron, but transforming in the fundamental repre-
sentation of SU (3). The non-abelian gauge theory of the strong force is called
Quantum Chromodynamics (QCD).
The use of QCD to describe the strong force was motivated by a whole series of
experimental and theoretical discoveries made in the 1960s and 1970s, involving the
symmetries and high-energy behavior of the strong interactions. But classical non-
abelian gauge theory is very diﬀerent from the observed world of strong interactions;
for QCD to describe the strong force successfully, it must have at the quantum
level the following three properties, each of which is dramatically diﬀerent from the
behavior of the classical theory:
(1) It must have a “mass gap;” namely there must be some constant ∆ > 0
such that every excitation of the vacuum has energy at least ∆.
(2) It must have “quark conﬁnement,” that is, even though the theory is de-
scribed in terms of elementary ﬁelds, such as the quark ﬁelds, that transform
non-trivially under SU (3), the physical particle states—such as the proton,
neutron, and pion—are SU (3)-invariant.
(3) It must have “chiral symmetry breaking,” which means that the vacuum is
potentially invariant (in the limit, that the quark-bare masses vanish) only
under a certain subgroup of the full symmetry group that acts on the quark
ﬁelds.
The ﬁrst point is necessary to explain why the nuclear force is strong but short-
ranged; the second is needed to explain why we never see individual quarks; and
the third is needed to account for the “current algebra” theory of soft pions that
was developed in the 1960s.
Both experiment—since QCD has numerous successes in confrontation with
experiment—and computer simulations, see for example [8], carried out since the
late 1970s, have given strong encouragement that QCD does have the properties
cited above. These properties can be seen, to some extent, in theoretical calcula-
tions carried out in a variety of highly oversimpliﬁed models (like strongly coupled
lattice gauge theory, see, for example, [48]). But they are not fully understood
theoretically; there does not exist a convincing, whether or not mathematically
complete, theoretical computation demonstrating any of the three properties in
QCD, as opposed to a severely simpliﬁed truncation of it.
