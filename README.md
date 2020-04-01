# Twisted Hodge numbers for complete intersections

The file `twisted.sage` implements the computation of twisted Hodge numbers for complete intersections, due to Brückmann in the following papers

* [MR0399102] Brückmann, Peter: Zur Kohomologie von projektiven Hyperflächen.
  Beiträge zur Algebra und Geometrie, 2. 4 (1973), 87–101 (1974).

* [MR0417202] Brückmann, Peter: Zur Kohomologie von vollständigen Durchschnitten mit Koeffizienten in der Garbe der Keime der Differentialformen.
  Math. Nachr. 71 (1976), 203–210.

* [MR0447266] Brückmann, Peter: Zur Kohomologie von vollständigen Durchschnitten mit Koeffizienten in der Garbe der Keime der Differentialformen. II.
  Math. Nachr. 77 (1977), 307–318.

## Getting started

Make sure that Sage knows about `twisted.sage`, probably by doing `load("twisted.sage")`. There is ample documentation in the file, which can be acessed via

```
twisted_hodge_number?
TwistedHodgeDiamond?
```

To get the (untwisted) Hodge diamond of a quartic surface, use

```sage
sage: print(TwistedHodgeDiamond((3, 4)))
          1
      0        0
  1       20       1
      0        0
          1
```

This luckily agrees with the output for

```sage
sage: print(TwistedHodgeDiamond((4, [3, 2])))
sage: print(TwistedHodgeDiamond((5, [2, 2, 2])))
```

If you rather care about *twisted* Hodge diamonds (otherwise you could also use the [Hodge diamond cutter](https://github.com/pbelmans/hodge-diamond-cutter)), you can add a twist parameter. For example, to compute the twisted Hodge diamond for projective 3-space, twisted by `O(4)` (so that we are in fact computing the Hochschild-Kostant-Rosenberg decomposition of Hochschild cohomology) as follows

```sage
sage: print(TwistedHodgeDiamond((3, []), 4))
                0
           0         0
      0         0        0
  1        0         0       0
      15        0        0
           45        0
                35
```

For more information, see the docstrings.

Also check out the documentation for the auxiliary class `CompleteIntersection`, and if you are into Hochschild cohomology the class `PolyvectorParallelogram`.

## Authors

* [**Pieter Belmans**](https://pbelmans.ncag.info)
* **Piet Glas**

