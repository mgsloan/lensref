
# lensref: Lens References

## What are lens references?

They are references which can be joined and on which lenses can be applied.
More documentation can be found in the `docs` directory:
[Introduction to state-based FRP (pdf)](https://github.com/divipp/lensref/blob/master/docs/Introduction.pdf)

The lensref package provides and interface an two implementation for lens references.

* The pure implementation is slow and has memory leaks but probably easier to follow. This is the reference implementation, so if the the other implementation differs this has the right behaviour.
* The fast implementation is intended for real usage.

## Status

* The interface is getting stable. You can expect more functionality and minor changes on current functionality.
* There are test cases for the first half of the interface. Both implementations fulfil the test cases.
* The pure implementation is ready.
* The fast implementation is much faster than the pure implementation, but it is far from being as fast as possible. Probably it also leaks memory.

## Usage

Only some Haddock documentation is available at the moment.

To see what is possible to do with lens references, look at the test cases in module `Data.LensRef.Test`.


## Links

* [Introduction to state-based FRP (pdf)](https://github.com/divipp/lensref/blob/master/docs/Introduction.pdf)
* [Haddock documentation on HackageDB](http://hackage.haskell.org/package/lensref)
* [Wordpress blog](http://lgtk.wordpress.com/)
* [haskell.org wiki page](http://www.haskell.org/haskellwiki/LGtk)
* [GitHub repository (this page)](https://github.com/divipp/lensref)



