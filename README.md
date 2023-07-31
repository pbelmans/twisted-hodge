[![DOI](https://zenodo.org/badge/220016736.svg)](https://zenodo.org/badge/latestdoi/220016736)

# Twisted Hodge numbers for complete intersections

The file `twisted.py` implements the computation of twisted Hodge numbers for complete intersections, due to Brückmann in the following papers

* [MR0399102] Brückmann, Peter: Zur Kohomologie von projektiven Hyperflächen.
  Beiträge zur Algebra und Geometrie, 2. 4 (1973), 87–101 (1974).

* [MR0417202] Brückmann, Peter: Zur Kohomologie von vollständigen Durchschnitten mit Koeffizienten in der Garbe der Keime der Differentialformen.
  Math. Nachr. 71 (1976), 203–210.

* [MR0447266] Brückmann, Peter: Zur Kohomologie von vollständigen Durchschnitten mit Koeffizienten in der Garbe der Keime der Differentialformen. II.
  Math. Nachr. 77 (1977), 307–318.
  
If you have used this code in any way, please consider citing it as explained on [Zenodo](https://doi.org/10.5281/zenodo.7006757). You can choose to cite a specific version, or the library in general.

## Getting started

It suffices to put ``twisted/twisted.py`` in your directory and load it using ``load("twisted.py")`` in Sage to get started.

Alternatively you can install it as follows:

``sage --pip install git+https://github.com/pbelmans/twisted-hodge.git``

and then you can use

``from twisted import *``

to use it.

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


## Instructions to myself

To perform the unit tests:

```
sage -t twisted/twisted.py
```

## Authors

* [**Pieter Belmans**](https://pbelmans.ncag.info)
* **Piet Glas**

