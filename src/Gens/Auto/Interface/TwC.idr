module Gens.Auto.Interface.TwC

import public Gens.Auto.Interface.Common
import public Spec.TwC


%default total


genTwC : Fuel -> Gen MaybeEmpty (color ** TwC color)
