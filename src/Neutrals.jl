"""

Package `Neutrals` provides two constants, `𝟘` and `𝟙` (with aliases `ZERO` and `ONE`),
which are neutral elements for respectively the addition and the multiplication of numbers.
In other words, whatever the type and the value of the number `x`, `x + 𝟘` and `𝟙*x` yield
`x` unchanged. In addition, `𝟘` is a *strong zero* in the sense that `𝟘*x` yields `𝟘` (or
`𝟘*unit(x)` if `x` has units) even though `x` may be infinite of a NaN (Not-a-number).

"""
module Neutrals

export Neutral, ZERO, ONE

using TypeUtils
using TypeUtils: @public
@public(
    @dispatch_on_value,
    Dispatch,
    dispatch,
    infinity,
    recode!,
    recode,
    static_value,
    type_common, # FIXME delete
    type_signed, # FIXME delete
)

include("types.jl")
include("dispatch.jl")
include("methods.jl")

# FIXME cleanup
@deprecate is_dimensionless(x) TypeUtils.is_unitless(x) false

end
