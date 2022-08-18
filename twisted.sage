r"""
Compute twisted Hodge numbers for complete intersections.

Implements Brückmann's formulae for the dimension of twists of exterior powers
of the cotangent bundle on complete intersections. This in particular computes
the usual Hodge diamond, and the polyvector parallelogram describing the
Hochschild-Kostant-Rosenberg decomposition for Hochschild cohomology.

These formulae are taken from

[MR0399102] Brückmann, Peter: Zur Kohomologie von projektiven Hyperflächen.
  Beiträge zur Algebra und Geometrie, 2. 4 (1973), 87–101 (1974).

[MR0417202] Brückmann, Peter: Zur Kohomologie von vollständigen Durchschnitten
  mit Koeffizienten in der Garbe der Keime der Differentialformen.
  Math. Nachr. 71 (1976), 203–210.

[MR0447266] Brückmann, Peter: Zur Kohomologie von vollständigen Durchschnitten
  mit Koeffizienten in der Garbe der Keime der Differentialformen. II.
  Math. Nachr. 77 (1977), 307–318.

They will be referred to as [1], [2] and [3] respectively.


EXAMPLES::

To compute the usual Hodge number `\mathrm{h}^{1,1}` of a quartic surface::

    sage: twisted_hodge_number((3, 4), 0, 1, 1)
    20

To compute the whole (untwisted) Hodge diamond of a quartic surface::

    sage: TwistedHodgeDiamond((3, 4))
              1
          0        0
      1       20       1
          0        0
              1

AUTHORS:

- Pieter Belmans and Piet Glas (2019-11-01): initial version

"""


def twisted_hodge_number(X, j, p, q):
    r"""Compute the twisted Hodge number of a complete intersection ``X``

    INPUT:

    - ``X``: a complete intersection, or a pair `(N, [d1, ..., dk])`
             describing one

    - ``j``: twist

    - ``p``: exterior power of the cotangent bundle

    - ``q``: cohomological degree

    OUTPUT: `\dim \mathrm{H}^q(X,\Omega_X^p(j))`

    EXAMPLES::

    We can compute the middle Hodge number of a complete intersection K3
    surface in the three cases as follows::

        sage: K3 = CompleteIntersection(3, 4)
        sage: twisted_hodge_number(K3, 0, 1, 1)
        20
        sage: K3 = CompleteIntersection(4, [3, 2])
        sage: twisted_hodge_number(K3, 0, 1, 1)
        20
        sage: K3 = CompleteIntersection(5, [2, 2, 2])
        sage: twisted_hodge_number(K3, 0, 1, 1)
        20

    We can compute the global sections of the tangent bundle on the quadric
    surface as follows, via the isomorphism `\Omega_Q^1(2)=\mathrm{T}_Q`::

        sage: Q = CompleteIntersection(3, 2)
        sage: twisted_hodge_number(Q, 2, 1, 0)
        6

    If you don't wish to construct the `CompleteIntersection` yourself, you
    can also just give the required data as follows::

        sage: twisted_hodge_number((3, 2), 2, 1, 0)
        6


    """
    def binom(n, k):
        """Wrap Sage's ``binomial`` such that we get 0 for negative ``n``."""
        if n < k or n < 0:
            return 0
        else:
            return binomial(n, k)

    def psi(n, r, p):
        """Implement equation (8) from [1]."""
        return binom(p - 1, r) * binom(p + n - r, n - r)

    def chi(d, m, p):
        """Implement equation (18) from [1]."""
        return binom(p + d + 1, d + 1) - binom(p + d + 1 - m, d + 1)

    def varphi(d, m, r, p):
        """Implement the first function in equation (29) from [1]."""
        return binom(p - 1, r) * binom(p + d + 1 - r, d + 1 - r) \
            + sum([(-1)**i * binom(d + 2, r + 1 - i)
                   * binom(p + d - i * (m-1) - r, d + 1)
                   for i in range(1, r + 2)])

    def sigma(d, m, p):
        """Implement the first function in equation (29) from [1]."""
        return sum([(-1)**i * binom(d + 2, i)
                    * binom(-p - (i-1) * (m-1), d + 1) for i in range(d + 3)])

    def alpha(n, m_i, p):
        """Implement the helper function from Lemma 1 from [2]."""
        # deal with the non-desirable way that Sage deals with combinations
        # and repetitions by ensuring uniqueness using ``enumerate``
        # there is probably a nicer way of doing this
        combinations = [[pair[1] for pair in m_i_mu]
                        for m_i_mu in Combinations(enumerate(m_i))]

        return binom(p + n, n) \
            + sum([(-1)**(len(m_i_mu)) * binom(p + n - sum(m_i_mu), n)
                   for m_i_mu in combinations if len(m_i_mu) != 0])

    # let's (try to) make it a complete intersection
    if not isinstance(X, CompleteIntersection):
        (n, d) = X
        X = CompleteIntersection(n, d)

    # necessarily 0 in this case
    if p < 0 or q < 0 or p > X.dimension or q > X.dimension:
        return 0

    # reduce projective space to linear section, for uniform treatment
    if X.is_projective_space:
        Y = CompleteIntersection(X.dimension + 1, [1])
        return twisted_hodge_number(Y, j, p, q)

    # we are working in the setting of [1]
    if X.is_hypersurface:
        # we switch to the notation of [1]
        d = X.dimension
        m = X.degree
        K = X.canonical_degree

        # Brückmann shuffles these variables around
        (r, q, p) = (p, q, j)

        # apply [Lemma 5, 1], equation (19)
        if r == 0:
            if q == 0:
                # apply first case of equation (19) from [1]
                return chi(d, m, p)
            elif q == X.dimension:
                # apply third case of equation (19) from [1]
                return chi(d, m, K - p)
            else:
                # apply second case of equation (19) from [1]
                return 0
        # apply [Lemma 5, 1], equation (20)
        elif r == d:
            if q == 0:
                # apply first case of equation (20) from [1]
                return chi(d, m, K + p)
            elif q == X.dimension:
                # apply third case of equation (20) from [1]
                return chi(d, m, -p)
            else:
                # apply second case of equation (20) from [1]
                return 0

        # apply [Satz 2, 1]
        elif r in range(1, X.dimension):
            if q == 0:
                # apply equation (38) from [1]
                return varphi(d, m, r, p)
            if q in range(1, d):
                if q + r != d:
                    # apply equation (39) from [1]
                    return kronecker_delta(q, r) * kronecker_delta(p, 0)
                else:
                    # apply equation (40) from [1]
                    return sigma(d, m, p - r*m) \
                           + kronecker_delta(d, 2*r) * kronecker_delta(p, 0)
            elif q == X.dimension:
                # apply equation (41) from [1]
                return varphi(d, m, d - r, -p)
            else:
                return 0
    # it's a complete intersection, so we are working in the setting of [2]
    else:
        # we switch to the notation of [2]
        Y = X
        (n, d, mi) = (Y.ambient_dimension, Y.dimension, Y.degrees)
        K = Y.canonical_degree

        X = Y.unsect()
        m = mi[-1]

        # Brückmann shuffles these variables around
        (r, q, p) = (p, q, j)

        # apply recursion from [Satz 5(5.1), 3]
        if q in range(1, d - r):
            # last two terms are omitted because we are in characteristic 0
            return twisted_hodge_number(X, p, r, q)
        # global sections
        elif q == 0:
            # apply first case of equation (10) from [2]
            if r == 0:
                return alpha(n, mi, p)
            # apply first case of equation (11) from [2]
            elif r == d:
                return alpha(n, mi, K + p)
            # apply recursion from [Satz 5(5.2), 3]
            elif r in range(1, d):
                # last term is omitted because we are in characteristic 0
                return twisted_hodge_number(X, p, r, 0) \
                       - twisted_hodge_number(X, p - m, r, 0) \
                       - twisted_hodge_number(Y, p - m, r - 1, 0) \
                       + twisted_hodge_number(X, p - m, r, 1)
            else:
                return 0
        # top degree cohomology
        elif q == d:
            # apply third case of equation (10) from [2]
            if r == 0:
                return alpha(n, mi, K - p)
            # apply third case of equation (11) from [2]
            elif r == d:
                return alpha(n, mi, -p)
            # apply Serre duality
            elif r in range(1, d):
                return twisted_hodge_number(Y, -p, d - r, 0)
            else:
                return 0
        # apply recursion from [Satz 5(5.3), 3]
        elif q == 1 and r == d - 1:
            return sum([(-1)**i * twisted_hodge_number(X, p, d, i) for i in range(3)]) \
                   - sum([(-1)**i * twisted_hodge_number(X, p + m, d, i) for i in range(2)]) \
                   + twisted_hodge_number(Y, p, d - 1, 0) \
                   + twisted_hodge_number(Y, p + m, d, 0)
        # apply recursion from [Satz 5(5.4), 3]
        elif r in range(1, d) and q == d - r:
            # last two terms are added because we are in characteristic 0
            return twisted_hodge_number(Y, p + m, r + 1, d - r - 1) \
                   - twisted_hodge_number(X, p, r + 1, d - r) \
                   + twisted_hodge_number(X, p + m, r + 1, d - r) \
                   - twisted_hodge_number(X, p + m, r + 1, d - r - 1) \
                   + twisted_hodge_number(X, -p, d - r, r) \
                   + twisted_hodge_number(Y, p, r, d - r - 1) \
                   - twisted_hodge_number(Y, -p - m, d - r - 1, r)
        # apply Serre duality to reduce to [Satz 5(5.1), 3]
        elif q in range(d - r + 1, d + 1):
            return twisted_hodge_number(Y, -p, d - r, d - q)

    raise ValueError("Twisted Hodge numbers are not defined for this input.")


class CompleteIntersection:
    r"""
    Construct a complete intersection, which is a container for invariants.

    This class is mostly just a helper class for the computation of twisted
    Hodge numbers, by abstracting away certain computations of invariants
    of complete intersections. It also allows for the construction of new
    complete intersections from old.

    EXAMPLES::

    We can construct a complete intersection with no hypersurfaces::

        sage: CompleteIntersection(3, [])

    We can construct a hypersurface::

        sage: CompleteIntersection(3, 4)
        sage: CompleteIntersection(3, [4])

    We can construct a complete intersection::

        sage: CompleteIntersection(4, [3, 2])

    We can construct intersections and unsections::

        sage: X = CompleteIntersection(4, [3, 2])
        sage: X.unsect()
        sage: X.intersect(3)
    """
    def __init__(self, N, d):
        r"""
        INPUT:

        - ``N``: dimension of the ambient projective space `\mathbb{P}^N`

        - ``d``: degrees of hypersurfaces (or a single degree), can be empty
        """
        try:
            len(d)
        except TypeError:
            d = [d]

        assert N >= 0, "ambient projective space must be non-empty"
        assert len(d) <= N, "complete intersection must be non-empty"
        assert all([di > 0 for di in d]), "degrees must be positive"

        self.__N = N
        self.__d = d

    def __str__(self):
        """Pretty print the complete intersection."""
        if self.is_projective_space:
            return ("{}-dimensional projective space".format(self.dimension))
        elif self.is_hypersurface:
            return ("Hypersurface of degree {} in {}-dimensional projective "
                    "space".format(self.degree, self.ambient_dimension))
        else:
            return ("{}-dimensional complete intersection of multidegree {} "
                    "in {}-dimensional projective space".format(
                        self.dimension, self.degrees, self.ambient_dimension))

    @property
    def degree(self):
        """Return the degree of the hypersurface, if it is one."""
        assert self.is_hypersurface

        return self.__d[0]

    @property
    def degrees(self):
        """Return the degrees of the hypersurfaces."""
        return self.__d

    @property
    def ambient_dimension(self):
        """Return the dimension of the ambient projective space"""
        return self.__N

    @property
    def codimension(self):
        """Return the codimension of the complete intersection."""
        return len(self.__d)

    @property
    def dimension(self):
        """Return the dimension of the complete intersection."""
        return self.ambient_dimension - self.codimension

    @property
    def is_hypersurface(self):
        """Check whether the complete intersection is a hypersurface."""
        return len(self.__d) == 1

    @property
    def is_projective_space(self):
        """Check whether there are no hypersurfaces whatsoever."""
        return len(self.__d) == 0

    @property
    def canonical_degree(self):
        """Return the degree of the canonical divisor."""
        return - self.ambient_dimension - 1 + sum(self.__d)

    def unsect(self):
        """Remove the last hypersurface from the complete intersection.

        EXAMPLES::

        Intersection of quadric and cubic becomes quadric::

            sage: X = CompleteIntersection(4, [2, 3])
            sage: Y = X.unsect()
            sage: Y.degree
            2

        By doing another unsection we get projective space itself::

            sage: Z = X.unsect()
            sage: Z.dimension
            4

        """
        assert not self.is_projective_space, "Cannot unsect projective space"

        return CompleteIntersection(self.ambient_dimension, self.degrees[:-1])

    def intersect(self, e):
        """Create further complete intersection with degree ``e`` hypersurface.

        INPUT:

        - ``e``: degree of new hypersurface

        EXAMPLES::

        Cut down a quadric surface by a cubic to get curve

            sage: X = CompleteIntersection(3, 2)
            sage: Y = X.intersect(3)
            sage: Y.degrees
            [2, 3]
        """
        assert self.dimension >= 1, "Need positive-dimensional original variety"
        return CompleteIntersection(self.ambient_dimension, self.degrees + [e])


class TwistedHodgeDiamond:
    r"""
    Container structure for twisted Hodge diamond.

    Mostly a convenient data structure containing twisted Hodge numbers of a
    complete intersection `X`, with the option for pretty printing, and
    further twisting.

    EXAMPLES::

    The (untwisted) Hodge diamond of a (quartic) K3 surface::

        sage: print(TwistedHodgeDiamond((3, 4)))
                  1
              0        0
          1       20       1
              0        0
                  1


    The twisted Hodge diamond of the projective plane, twisted by `O(3)`::

        sage: print(TwistedHodgeDiamond((2, []), 3))
                  0
              0        0
          1       0        0
              8        0
                  10
        ...

    """
    __M = []

    def __init__(self, X, j=0):
        """
        INPUT:

        - ``X``: a complete intersection, or a pair `(N, [d1, ..., dk])`
                 describing one

        - ``j``: degree of the twist
        """
        # let's (try to) make it a complete intersection
        if not isinstance(X, CompleteIntersection):
            (n, d) = X
            X = CompleteIntersection(n, d)

        self.__X = X
        self.__j = j

        self.__M = zero_matrix(j.parent(), X.dimension + 1)

        for (p, q) in cartesian_product([range(X.dimension + 1)]*2):
            self.__M[p, q] = twisted_hodge_number(X, j, p, q)
        # if the need arises one could use memoization here

    def pprint(self):
        """Return the parallelogram as a Sage table object"""
        T = []
        d = self.variety.dimension

        for i in reversed(range(2*d + 1)):
            row = [""]*(abs(d - i))

            for j in range(max(0, i - d), min(i, d) + 1):
                row.extend([self.__M[i - j, j], ""])

            T.append(row)

        # padding all rows to full length
        for i in range(len(T)):
            T[i].extend([""]*(2*d - len(T[i]) + 1))

        return table(T, align="center")

    def __str__(self):
        return str(self.pprint())

    def __getitem__(self, key):
        r"""Return $\mathrm{h}_j^{p,q}(X)$.

        INPUT:

        - ``key``: tuple of indices for the (twisted) Hodge diamond
        """
        (p, q) = key
        return self.__M[p, q]

    @property
    def variety(self):
        return self.__X

    def twist(self, i):
        """Create new twisted Hodge diamond, twisted by ``i+j``.

        INPUT:

        - ``i``: degree of further twist
        """
        return TwistedHodgeDiamond(self.__X, self.__j + i)


class PolyvectorParallelogram(TwistedHodgeDiamond):
    r"""
    Container structure for polyvector parallelograms.

    This is a convenient way of writing down the twisted Hodge diamond, when
    twisting by the anticanonical bundle. This

    It puts the relevant part of the (extended) deformation given by
    Hochschild cohomology on top.

    EXAMPLES::

    The polyvector parallelogram of a cubic surface starts is::

        sage: print(PolyvectorParallelogram((3, 3)))
          1
          0   0
          0   4   4
              0   0
                  0

    Here the first row tells us that the surface is connected. The second row
    being zero comes from the fact that the dimension of the Picard group is
    zero, and that the automorphism group is discrete. The third line tells us
    that there are no gerby deformations, and both 4 commutative and 4 non-
    commutative deformation directions. The fourth line being zero tells us
    that there are no obstructions whatsoever, and the fifth line does not
    have a deformation-theoretic interpretation.
    """
    def __init__(self, X):
        """
        INPUT:

        - ``X``: a complete intersection, or a pair `(N, [d1, ..., dk])`
          describing one.
        """
        # let's (try to) make it a complete intersection
        if not isinstance(X, CompleteIntersection):
            (n, d) = X
            X = CompleteIntersection(n, d)

        TwistedHodgeDiamond.__init__(self, X, -X.canonical_degree)

    def pprint(self):
        """Return the parallelogram as a Sage table object"""
        T = []
        d = self.variety.dimension

        for n in range(2*d + 1):
            T.append([])

            for q in range(d + 1):
                p = n - q
                if q in range(d + 1) and p in range(d + 1):
                    T[-1].append(self[q, p])
                else:
                    T[-1].append("")

        return str(table(T, align="center"))

    def __str__(self):
        return str(self.pprint())

    def __getitem__(self, key):
        """Return $\\mathrm{h}^q(X,\\bigwedge^p\\mathrm{T}_X)$.

        This modifies the getter from the underlying twisted Hodge diamond.

        INPUT:

        - ``key``: tuple of indices for the (twisted) Hodge diamond
        """
        (p, q) = key
        d = self.variety.dimension
        return TwistedHodgeDiamond.__getitem__(self, (d - p, q))
