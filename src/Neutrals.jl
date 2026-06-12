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
    adapt_multiplier_precision,
    dispatch,
    impl_add,
    impl_and,
    impl_cmp,
    impl_div,
    impl_eq,
    impl_inv,
    impl_isless,
    impl_le,
    impl_lshft,
    impl_lt,
    impl_mod,
    impl_mul,
    impl_or,
    impl_pow,
    impl_rem,
    impl_rshft,
    impl_sub,
    impl_tdv,
    impl_urshft,
    impl_xor,
    is_dimensionless,
    is_static_number,
    recode!,
    recode,
    type_common,
    type_signed,
    value,
)

if !isdefined(Base, :get_extension)
    using Requires
end

include("types.jl")
include("dispatch.jl")
include("basics.jl")
include("binary-operations.jl")

function __init__()
    @static if !isdefined(Base, :get_extension)
        # Extend methods when other packages are loaded.
        @require Unitful = "1986cc42-f94f-5a68-af5c-568840ba703d" include(
            "../ext/NeutralsUnitfulExt.jl")
    end
end

end
