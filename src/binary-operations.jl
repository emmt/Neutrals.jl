#----------------------------------------------------------------------- Binary operations -

"""
    using Test
    Neutrals.test_binary_operations(x...)

Test binary operations between each of the values in `x...` and each of the neutral number
instances.

This function is intended to be called in a `@testset` block.

"""
function test_binary_operations end

# For some binary operations involving neutral numbers, it is sufficient to apply the base
# method for the arguments promoted according to promotion rules. Other operations must be
# specialized either because the operation has a specific "hard-coded" result (e.g. `𝟙*x ->
# x` or `x + 𝟘 -> x`) or because the promotion rules are inappropriate. In this package,
# such base methods are extended when at least one the operand is a neutral number (without
# specializing on the specific value of the neutral operand, hence, for type `Neutral` in
# the signature of the method) to call an implementation of the operation named
# `Neutrals.impl_$op` where `$op` is the name of the operation (e.g., `add` for `+`).
# Methods implementing binary operations are public but not exported and can be specialized
# for specific values of the neutral argument and/or type of the other argument.
# Implementations of binary operations when both arguments are neutral number are
# automatically encoded when the package is built.
#
# To infer which method is called for a given function and types of arguments, `methods(f,
# types)` is your friend:
#
#     +(x::Integer,  y::Integer)  in `base/int.jl`
#     +(x::Integer,  y::Rational) in `base/rational.jl`
#     +(x::Rational, x::Integer)  in `base/rational.jl`
#     +(x::Integer,  y::BigInt)   in `base/gmp.jl`
#     +(x::BigInt,   x::Integer)  in `base/gmp.jl`
#
# similarly for `-`, for comparing numbers:
#
#     ==(x::Number, y::Number) in `base/promotion.jl`
#     <( x::Real, y::Real)     in `base/promotion.jl`
#     <=(x::Real, y::Real)     in `base/promotion.jl`
#
# and so on.
#
# Override base methods to call corresponding implementation when at least one of the operands is
# a neutral number:
for (f, (g, Ts)) in [:(+)   => (:impl_add,    [:Number, :Real, :Integer, :Rational,
                                               :Complex, :(Complex{Bool}), :AbstractIrrational,
                                               :AbstractFloat, :BigInt, :BigFloat]),
                     :(-)   => (:impl_sub,    [:Number, :(Complex{Bool}), :Real, :Integer, :Rational,
                                               :Complex, :AbstractIrrational,
                                               :AbstractFloat, :BigInt, :BigFloat]),
                     :(*)   => (:impl_mul,    [:Number, :Real, :Integer,
                                               :Rational, :Complex, :(Complex{Bool})]),
                     :(/)   => (:impl_div,    [:Number, :Real, :Integer, :Rational,
                                               :Complex, :(Complex{Bool})]),
                     :(^)   => (:impl_pow,    [:Number, :Real, :Integer, :Rational,
                                               :AbstractIrrational, :(Irrational{:ℯ}),
                                               :Float16, :Float32, :Float64,
                                               :(Union{Float16, Float32}), # <- needed to avoid ambiguities with Julia 1.12
                                               :Complex, :(Complex{<:AbstractFloat}),
                                               :(Complex{<:Integer}), :(Complex{<:Rational}),
                                               :BigInt, :BigFloat]),
                     :div   => (:impl_tdv,    [:Real, :Rational]),
                     :rem   => (:impl_rem,    [:Real, :Rational]),
                     :mod   => (:impl_mod,    [:Real, :Rational]),
                     :(==)  => (:impl_eq,     [:Number, :Real, :Rational,
                                               :AbstractIrrational, :Complex,
                                               :BigInt, :BigFloat]),
                     :(<)   => (:impl_lt,     [:Real, :Rational, :BigInt, :BigFloat]),
                     :(<=)  => (:impl_le,     [:Real, :Rational, :BigInt, :BigFloat]),
                     :cmp   => (:impl_cmp,    [:Number, :Real, :Integer,
                                               :BigInt, :BigFloat]),
                     :(|)   => (:impl_or,     [:Integer,]),
                     :(&)   => (:impl_and,    [:Integer,]),
                     :xor   => (:impl_xor,    [:Integer,]),
                     :(<<)  => (:impl_lshft,  [:Integer, :Bool, :Int]),
                     :(>>)  => (:impl_rshft,  [:Integer, :Bool, :Int]),
                     :(>>>) => (:impl_urshft, [:Integer, :Bool, :Int]),
                     ]
    @eval Base.$f(x::Neutral, y::Neutral) = $g(x, y)
    for T in Ts
        @eval Base.$f(x::Neutral, y::$T) = $g(x, y)
        @eval Base.$f(x::$T, y::Neutral) = $g(x, y)
    end
end

# Encode implementation of some binary operators/functions when both operands are neutral
# numbers. For other binary operators/functions, the base methods are assumed to work thanks
# to the implemented promotion rules.
for x in instances(Neutral), y in instances(Neutral)
    for (f, g) in [:(+)   => :impl_add,
                   :(-)   => :impl_sub,
                   :(*)   => :impl_mul,
                   :(==)  => :impl_eq,
                   :(<)   => :impl_lt,
                   :(<=)  => :impl_le,
                   :cmp   => :impl_cmp,
                   :(|)   => :impl_or,
                   :(&)   => :impl_and,
                   :(xor) => :impl_xor,
                   :(<<)  => :impl_lshft,
                   :(>>)  => :impl_rshft,
                   :(>>>) => :impl_urshft]
        # Compute the result based on the integer values of the neutral operands and
        # implement function that returns a neutral number if possible or the integer result
        # otherwise.
        r = @eval $f(Int($x), Int($y))
        if f !== :cmp && r isa Int && r ∈ (0, 1, -1)
            @eval $g(x::$(typeof(x)), y::$(typeof(y))) = $(Neutral{r}())
        else
            @eval $g(x::$(typeof(x)), y::$(typeof(y))) = $r
        end
    end

    # Implement Euclidean division (taking care of division by zero).
    for (f, g) in [:(/) => :impl_div,
                   :div => :impl_tdv,
                   :rem => :impl_rem,
                   :mod => :impl_mod]
        if iszero(y)
            @eval $g(x::$(typeof(x)), y::$(typeof(y))) = throw(DivideError())
        else # y is ONE or -ONE
            r = if f === :(/)
                Int(x)*Int(y) # x/y yields the same result as x*y when abs(y) = 1
            else
                @eval $f(Int($x), Int($y))
            end
            @eval $g(x::$(typeof(x)), y::$(typeof(y))) = $(Neutral{r}())
        end
    end

    # Exponentiation.
    @eval impl_pow(x::$(typeof(x)), y::$(typeof(y))) = $(iszero(y) ? ONE : x)
end

"""
    Neutrals.impl_inv(x) -> 𝟙/x

Return multiplicative inverse of number `x`. Default to `inv(x)`.

"""
impl_inv(x::Number) = inv(x)
if VERSION < v"1.2.0-rc2"
    # `inv(x)` was not implemented for irrational numbers prior to Julia 1.2.0-rc2
    impl_inv(x::AbstractIrrational) = true/x
end

#------------------------------------------------------------ Arithmetic binary operations -

"""
    Neutrals.additive_operand(T, x::Neutral) -> xp

Return a value `xp` equivalent to that of `x` and with efficient type for an arithmetic
operation like the addition involving an operand of type `T` and operand `x`.

# See also

[`Neutrals.comparative_operand`](@ref) for comparison operations and
[`Neutrals.bitwise_operand`](@ref) for bitwise operations.

"""
function additive_operand(::Type{T}, x::Neutral) where {T<:Number}
    # The default implementation purposely throws if `T` has units or if `T` is a non-negative
    # type and `x` is `-𝟙`.
    return convert(T, Int(x))::T
end

function additive_operand(::Type{<:BigNumber}, x::Neutral)
    return x === -ONE ? Clong(-1) : Culong(Int(x))
end

function additive_operand(::Type{<:Bool}, x::Neutral)
    return Int(x)
end

function additive_operand(::Type{Rational{T}}, x::Neutral) where {T}
    return convert(T, Int(x))::T
end

function additive_operand(::Type{Complex{T}}, x::Neutral) where {T}
    return convert(T, Int(x))::T
end

"""
    Neutrals.impl_add(x, y) -> x + y

Implement addition of numbers `x` and `y` when at least one of the operands is a neutral
number. If this method is overridden, it is sufficient to specialize it when `y` is a
neutral number.

"""
impl_add(x::Neutral, y::Any) = impl_add(y, x) # addition is commutative

function impl_add(x::Number, y::Neutral)
    assert_dimensionless(:(+), x)
    if iszero(y) # x + 𝟘
        return x
    elseif isone(y) # x + 𝟙
        return x + additive_operand(typeof(x), ONE)
    else # x + -𝟙
        return x - additive_operand(typeof(x), ONE)
    end
end

function impl_add(x::Bool, y::Neutral)
    if iszero(y) # x + 𝟘
        return x ? 1 : 0
    elseif isone(y) # x + 𝟙
        return x ? 2 : 1
    else # x + -𝟙
        return x ? 0 : -1
    end
end

"""
    Neutrals.impl_sub(x, y) -> x - y

Implement subtraction of numbers `x` and `y` when at least one of the operands is a neutral
number.

"""
function impl_sub(x::Neutral, y::Number)
    assert_dimensionless(:(-), y)
    if iszero(x) # 𝟘 - y
        return -y
    elseif isone(x) # 𝟙 - y
        return additive_operand(typeof(y), ONE) - y
    else # -𝟙 - y
        return additive_operand(typeof(y), -ONE) - y
    end
end

function impl_sub(x::Number, y::Neutral)
    assert_dimensionless(:(-), x)
    if iszero(y) # x - 𝟘
        return x
    elseif isone(y) # x - 𝟙
        return x - additive_operand(typeof(x), ONE)
    else # x - -𝟙 -> x + 𝟙
        return x + additive_operand(typeof(x), ONE)
    end
end

function impl_sub(x::Neutral, y::Bool)
    if iszero(x) # 𝟘 - y
        return y ? -1 : 0
    elseif isone(x) # 𝟙 - y
        return y ? 0 : 1
    else # -𝟙 - y
        return y ? -2 : -1
    end
end

function impl_sub(x::Bool, y::Neutral)
    if iszero(y) # x - 𝟘
        return x ? 1 : 0
    elseif isone(y) # x - 𝟙
        return x ? 0 : -1
    else # x - -𝟙 -> x + 𝟙
        return x ? 2 : 1
    end
end

"""
    Neutrals.impl_mul(x, y) -> x * y    # if x and y are numbers
    Neutrals.impl_mul(x, y) -> x .* y   # if one of x or y is an array

Implement scalar or element-wise multiplication of `x` by `y` when at least one of the
operands is a neutral number while the other is a number or an array of numbers. If this
method is overridden, it is sufficient to specialize it when `x` is a neutral number.

"""
impl_mul(x::Any, y::Neutral) = impl_mul(y, x) # multiplication is commutative

function impl_mul(x::Neutral, y::Number)
    if iszero(x) # 𝟘 * y
        return zero(y)
    elseif isone(x) # 𝟙 * y
        return y
    else # -𝟙 * y
        return -y
    end
end

"""
    Neutrals.impl_div(x, y) -> x / y    # if x and y are numbers
    Neutrals.impl_div(x, y) -> x ./ y   # if one of x or y is an array

Implement scalar or element-wise division of `x` by `y` when at least one of the operands is
a neutral number while the other is a number or an array of numbers.

"""
function impl_div(x::Neutral, y::Number)
    if iszero(x) # 𝟘 / y
        # Strong zero ignores value of denominator (though not its units).
        return false/impl_oneunit(y) # NOTE this should compile to a constant
    elseif isone(x) # 𝟙 / y -> inv(y)
        return impl_inv(y)
    else # -𝟙 / y -> -inv(y)
        return -impl_inv(y)
    end
end

function impl_div(x::Number, y::Neutral)
    if iszero(y) # x / 𝟘
        return impl_inf(x) # ±Inf (never NaN)
    elseif isone(y) # x / 𝟙 -> x
        return x
    else # x / -𝟙 -> -x
        return -x
    end
end

impl_div(x::Complex, y::Neutral{0}) = complex(x.re/ZERO, x.im/ZERO)

impl_inf(x::AbstractFloat) = convert(typeof(x), ifelse(signbit(x), -Inf, Inf))
impl_inf(x::NonnegativeInteger) = Inf
impl_inf(x::Integer) = ifelse(signbit(x), -Inf, Inf)
impl_inf(x::Rational{T}) where {T<:NonnegativeInteger} = one(T)//zero(T)
impl_inf(x::Rational{T}) where {T<:Integer} = ifelse(signbit(x), -one(T), one(T))//zero(T)

"""
    Neutrals.impl_pow(x, y) -> x^y

Implements raising number `x` to the power `y` when `y` is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

"""
function impl_pow(x::Number, y::Neutral)
    if iszero(y)
        return impl_oneunit(x)
    elseif isone(y)
        return x
    else
        return impl_inv(x)
    end
end

function impl_pow(x::Neutral, y::Number)
    assert_dimensionless(:(^), y)
    if iszero(x) # 𝟘^y
        return zero(y)
    elseif isone(x) # 𝟙^y
        return one(y)
    else # (-𝟙)^y
        if y isa Integer
            # Note that `convert` may throw depending on the type of `y` so we cannot use
            # `ifelse` here.
            return iseven(y) ? one(y) : convert(typeof(y), -1)
        else
            return (-one(y))^y
        end
    end
end

#---------------------------------------------------------------------- Euclidean division -

"""
    Neutrals.impl_tdv(x, y) -> x ÷ y

Implement the truncated division of `x` by `y` that is the quotient of `x` by `y` rounded
toward zero. This corresponds to `div(x,y,RoundToZero)`.

"""
function impl_tdv(x::Neutral, y::Number) # TODO check that n ± bool -> Int
    if iszero(x) # div(𝟘, y)
        return zero(impl_ustrip(typeof(y)))/impl_unit(y)
    elseif isone(x) # div(𝟙, y)
        return div(additive_operand(y, ONE), y)
    else # div(-𝟙, y) -> -div(𝟙, y)
        return div(additive_operand(y, -ONE), y)
    end
end

function impl_tdv(x::Number, y::Neutral)
    if iszero(y)
        # div(x, 𝟘) -> ±0
        is_integer(x) && throw(DivideError())
        return copysign(reciprocal_zero(x), x)
    elseif isone(y)
        # div(x, 𝟙) -> x if x integer
        is_integer(x) && return x
        return div(x, (x isa BigFloat ? Culong(1) : one(x)))
    else # div(x, -𝟙)
        # FIXME does not work if x unsigned
        return div(x, (x isa BigFloat ? Clong(-1) : -one(x)))
    end
end

"""
    Neutrals.impl_rem(x, y) -> rem(x, y)

Implement the remainder function when at least one of the operands is a neutral number.

The remainder function satisfies `x == div(x,y)*y + rem(x,y)` with `div` the truncated
division which yields the quotient rounded toward zero, implying that sign of `rem(x,y)`
matches that of `x`.

"""
impl_rem

"""
    Neutrals.impl_mod(x, y) -> mod(x, y)

Implement `mod` when at least one of the operands is a neutral number.

The modulus function satisfies `x == fld(x,y)*y + mod(x,y)`, with `fld` the floored division
which yields the rounded towards `-Inf`, implying that sign of `mod(x,y)` matches that of
`y`.

""" impl_mod

# In Julia, `div` and `rem` yield a result of the signedness of the 1st operand, while
# `mod` yields a result of the signedness of the 2nd operand. For these operations, a
# neutral number is thus converted to a signed value whose type is based on that of the
# other operand.
for (f, g) in (:div => :impl_tdv, :rem => :impl_rem, :mod => :impl_mod)
    @eval begin
        $g(x::Real, y::Neutral{0}) = throw(DivideError())
        $g(x::Real, y::Neutral) = $f(x, convert(type_signed(x), y))
        $g(x::Neutral, y::Real) = $f(convert(type_signed(y), x), y)
    end
end

# Specialize implementation for integers (not Booleans) and for `±𝟙` considering that
# neutral numbers are signed integers.
#
# Quotient of truncated division is of the signedness of the 1st operand.
impl_tdv(x::Integer, y::Neutral{1}) = x
#
# Remainder of truncated division is of the signedness of the `st operand.
impl_rem(x::Integer, y::Neutral{1}) = zero(x) # FIXME yield ZERO instead?
impl_rem(x::Signed, y::Neutral{-1}) = zero(x) # FIXME yield ZERO instead?
#
# Modulo is of the signedness of the 2nd operand and is 0 if 2nd operand is -1.
impl_mod(x::Integer, y::Neutral{1}) = zero(type_signed(x)) # FIXME yield ZERO instead?
impl_mod(x::Integer, y::Neutral{-1}) = zero(type_signed(x)) # FIXME yield ZERO instead?
#
# For Booleans, implementation of `div`, `rem`, and `mod` in `base/bool.jl` is:
#
#     div(x::Bool, y::Bool) = y ? x : throw(DivideError())
#     rem(x::Bool, y::Bool) = y ? false : throw(DivideError())
#     mod(x::Bool, y::Bool) = rem(x,y)
#
impl_tdv(x::Bool, y::Neutral{1}) = x
impl_rem(x::Bool, y::Neutral{1}) = false
impl_mod(x::Bool, y::Neutral{1}) = false
for f in (:impl_tdv, :impl_rem, :impl_mod)
    @eval $f(x::Bool, y::Neutral{-1}) = throw(InexactError(:convert, Bool, -ONE))
end

#----------------------------------------------------------------------------- Comparisons -

"""
    Neutrals.comparative_operand(T, x::Neutral)

Return a value equivalent to that of `x` and with efficient type for an ordered comparison
operation involving an operand of type `T` and operand `x`. Ordered comparisons include
`cmp`, `isless`, `<`, `<=`, `>`, or `>=`, but not `==` nor `isequal`.

# See also

[`Neutrals.additive_operand`](@ref) for arithmetic operations and
[`Neutrals.bitwise_operand`](@ref) for bitwise operations.

"""
comparative_operand(::Type{T}, x::Neutral{ 0}) where {T<:BareNumber} = zero(T)
comparative_operand(::Type{T}, x::Neutral{ 1}) where {T<:BareNumber} =  one(T)
comparative_operand(::Type{T}, x::Neutral{-1}) where {T<:BareNumber} = -one(T)

comparative_operand(::Type{T}, x::Neutral{ 0}) where {T<:BigNumber} = Culong(0)
comparative_operand(::Type{T}, x::Neutral{ 1}) where {T<:BigNumber} = Culong(1)
comparative_operand(::Type{T}, x::Neutral{-1}) where {T<:BigNumber} = Clong(-1)

@noinline comparative_operand(::Type{T}, x::Neutral{-1}) where {T<:NonnegativeNumber} =
    throw(InexactError(:convert, T, -1))

"""
    Neutrals.impl_eq(x, y) -> x == y

Implements `==` for numbers when at least one of the operands is a neutral number. If this
method is overridden, it is sufficient to specialize it when `y` is a neutral number.

"""
impl_eq(x::Neutral, y::Any) = impl_eq(y, x) # `==` is commutative

function impl_eq(x::Number, y::Neutral)
    # NOTE We assume that `iszero(x)` and `isone(x)` are not slower than `x == zero(x)` and
    #      `x == one(x)` an we specialize `x == -𝟙` to yield `false` for non-negative
    #      numbers (see below).
    is_dimensionless(x) || return false
    if iszero(y) # x == 𝟘
        return iszero(x)
    elseif y === ONE # x == 𝟙
        return isone(x)
    else # x == (-𝟙)
       return x == comparative_operand(typeof(x), -ONE)
    end
end

# `x == -𝟙` must be specialized to yield `false` for non-negative numbers.
impl_eq(x::NonnegativeNumber, y::Neutral{-1}) = false

# Optimize for Booleans.
impl_eq(x::Bool, y::Neutral{1}) = x
impl_eq(x::Bool, y::Neutral{0}) = !x

# Neutral numbers are integers and are thus never equal to irrational numbers.
impl_eq(x::AbstractIrrational, y::Neutral) = false

"""
    Neutrals.impl_lt(x, y) -> x < y

Implement `<` for real numbers when at least one of the operands is a neutral number.

"""
function impl_lt(x::Neutral, y::Number)
    assert_dimensionless(:(<), y)
    if iszero(x) # 𝟘 < y
        return comparative_operand(typeof(y), ZERO) < y
    elseif isone(x) # 𝟙 < y
        return comparative_operand(typeof(y),  ONE) < y
    else # -𝟙 < y
        return comparative_operand(typeof(y), -ONE) < y
    end
end
function impl_lt(x::Number, y::Neutral)
    assert_dimensionless(:(<), x)
    if iszero(y) # x < 𝟘
        return x < comparative_operand(typeof(x), ZERO)
    elseif isone(y) # x < 𝟙
        return x < comparative_operand(typeof(x),  ONE)
    else # x < -𝟙
        return x < comparative_operand(typeof(x), -ONE)
    end
end

# Optimize comparison of an unsigned real and a neutral number.
impl_lt(x::NonnegativeNumber, y::Neutral{ 0}) = false
impl_lt(x::NonnegativeNumber, y::Neutral{-1}) = false
impl_lt(x::Neutral{-1}, y::NonnegativeNumber) = true
#
impl_lt(x::Bool, y::Neutral{1}) = !x
impl_lt(x::Neutral{0}, y::Bool) = y
impl_lt(x::Neutral{1}, y::Bool) = false

"""
    Neutrals.impl_le(x, y) -> x ≤ y

Implement `≤` for real numbers when at least one of the operands is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

"""
function impl_le(x::Neutral, y::Number)
    assert_dimensionless(:(<=), y)
    if iszero(x)    # 𝟘 ≤ y
        return comparative_operand(typeof(y), ZERO) ≤ y
    elseif isone(x) # 𝟙 ≤ y
        return comparative_operand(typeof(y),  ONE) ≤ y
    else           # -𝟙 ≤ y
        return comparative_operand(typeof(y), -ONE) ≤ y
    end
end
function impl_le(x::Number, y::Neutral)
    assert_dimensionless(:(<=), x)
    if iszero(y)    # x ≤ 𝟘
        return x ≤ comparative_operand(typeof(x), ZERO)
    elseif isone(y) # x ≤ 𝟙
        return x ≤ comparative_operand(typeof(x),  ONE)
    else            # x ≤ -𝟙
        return x ≤ comparative_operand(typeof(x), -ONE)
    end
end

# Optimize comparison of an unsigned number.
impl_le(x::Neutral{-1}, y::NonnegativeNumber) = true
impl_le(x::NonnegativeNumber, y::Neutral{-1}) = false
#
impl_le(x::Bool, y::Neutral{0}) = !x
impl_le(x::Bool, y::Neutral{1}) = true
impl_le(x::Neutral{1}, y::Bool) = y

"""
    Neutrals.impl_cmp(x, y) -> cmp(x, y)

Implement `cmp` for real numbers when at least one of the operands is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

This method can be overridden by specializing it when the second operand is a neutral
number.

"""
impl_cmp(x::Neutral, y::Real) = -impl_cmp(y, x) # `cmp` is anti-commutative
impl_cmp(x::Integer, y::Neutral) =
    ifelse(impl_isless(x, y), -1, ifelse(impl_isless(y, x), 1, 0))
impl_cmp(x::Real, y::Neutral) =
    impl_isless(x, y) ? -1 : ifelse(impl_isless(y, x), 1, 0)

# Special cases.
impl_cmp(x::NonnegativeNumber, y::Neutral{-1}) = 1
impl_cmp(x::NonnegativeNumber, y::Neutral{ 0}) = iszero(x) ? 0 : 1
#
impl_cmp(x::Bool, y::Neutral{1}) = x ? 0 : -1

"""
    Neutrals.impl_isless(x, y) -> isless(x, y)

Implement `isless` for real numbers when at least one of the operands is a neutral number.

"""
function impl_isless(x::Neutral, y::Number)
    assert_dimensionless(:isless, y)
    if iszero(x) # isless( 𝟘, y)
        return isless(comparative_operand(typeof(y), ZERO), y)
    elseif isone(x) # isless( 𝟙, y)
        return isless(comparative_operand(typeof(y),  ONE), y)
    else # isless(-𝟙, y)
        return isless(comparative_operand(typeof(y), -ONE), y)
    end
end

function impl_isless(x::Number, y::Neutral)
    assert_dimensionless(:isless, x)
    if iszero(y) # isless(x,  𝟘)
        return isless(x, comparative_operand(typeof(x), ZERO))
    elseif isone(y) # isless(x,  𝟙)
        return isless(x, comparative_operand(typeof(x),  ONE))
    else # isless(x, -𝟙)
        return isless(x, comparative_operand(typeof(x), -ONE))
    end
end

# Special cases.
impl_isless(x::NonnegativeNumber, y::Neutral{-1}) = false
impl_isless(x::Neutral{-1}, y::NonnegativeNumber) = true

# NOTE For floats in `base/float.jl`:
#      isless(x, y) =  isnan(x) || isnan(b) ? !isnan(x) : x < y
impl_isless(x::AbstractFloat, y::Neutral) =
    isnan(x) ? false : x < oftype(x, Int(y))
impl_isless(x::Neutral, y::AbstractFloat) =
    isnan(y) ? true : oftype(y, Int(x)) < y

#---------------------------------------------------------------------- Bitwise operations -

# For bitwise operations (`|`, `&`, and `xor`) between integers (including Booleans and big
# integers) of mixed types, the called methods are defined in `base/int.jl` and promote
# their arguments before calling a more specialized method. When one operand is a neutral
# number, we override this method to implement optimized expressions. Even though the other
# operand is unsigned, we consider that `-𝟙` behaves as a constant of the same type with all
# its bits set to 1.

"""
    Neutrals.bitwise_operand(T, x::Neutral)::T

Return a value equivalent to that of `x` and with efficient type for a bitwise operation
involving an operand of type `T<:Integer` and operand `x`. For such an operation, if
`x = -ONE`, the result is an integer of type `T` whose bits are all equal to one.

# See also

[`Neutrals.additive_operand`](@ref) for arithmetic operations and
[`Neutrals.comparative_operand`](@ref) for comparison operations.

"""
bitwise_operand(::Type{T}, x::Neutral{ 0}) where {T<:Integer} =  zero(T)
bitwise_operand(::Type{T}, x::Neutral{ 1}) where {T<:Integer} =   one(T)
bitwise_operand(::Type{T}, x::Neutral{-1}) where {T<:Integer} = ~zero(T)

bitwise_operand(::Type{T}, x::Neutral{ 0}) where {T<:BigInt} = Culong(0)
bitwise_operand(::Type{T}, x::Neutral{ 1}) where {T<:BigInt} = Culong(1)
bitwise_operand(::Type{T}, x::Neutral{-1}) where {T<:BigInt} = Clong(-1)

"""
    Neutrals.impl_or(x, y) -> x | y

Implement `x | y` when one of the operands is a neutral number while the other is an
integer. If this method is overridden, it is sufficient to specialize it when `y` is a
neutral number.

"""
impl_or(x::Neutral, y::Any) = impl_or(y, x) # bitwise OR is commutative

function impl_or(x::Integer, y::Neutral)
    if iszero(y) # x | 𝟘
        return x
    elseif isone(y) # x | 𝟙
        return x | bitwise_operand(typeof(x), ONE)
    else # x | -𝟙
        return ~zero(x)
    end
end

# The following is twice faster than `~big(0)` or `~zero(BigInt)` because it creates a
# single big integer object.
impl_or(x::BigInt, y::Neutral{-1}) = BigInt(Clong(-1))::BigInt

# Optimize for Booleans.
impl_or(x::Bool, ::Neutral{ 1}) = true
impl_or(x::Bool, ::Neutral{-1}) = true

"""
    Neutrals.impl_and(x, y) -> x & y

Implement `x & y` when one of the operands is a neutral number while the other is an
integer. If this method is overridden, it is sufficient to specialize it when `y` is a
neutral number.

"""
impl_and(x::Neutral, y::Any) = impl_and(y, x) # bitwise AND is commutative

function impl_and(x::Integer, y::Neutral)
    if iszero(y) # x & 𝟘 -> 0
        return zero(x)
    elseif isone(y) # x & 𝟙
        return x & bitwise_operand(typeof(x), ONE)
    else # x & -𝟙 -> x
        return x
    end
end

# Optimize for Booleans.
impl_and(x::Bool, ::Neutral{1}) = x

"""
    Neutrals.impl_xor(x, y)

Implement `xor(x, y)` when one of the operands is a neutral number while the other is an
integer. If this method is overridden, it is sufficient to specialize it when `y` is a
neutral number.

"""
impl_xor(x::Neutral, y::Any) = impl_xor(y, x) # bitwise XOR is commutative

function impl_xor(x::Integer, y::Neutral)
    if iszero(y) # xor(x, 𝟘) -> x
        return x
    elseif isone(y) # xor(x, 𝟙)
        return xor(x, bitwise_operand(typeof(x), ONE))
    else # xor(x, -𝟙)
        return xor(x, bitwise_operand(typeof(x), -ONE))
    end
end

# Optimize for Booleans.
impl_xor(x::Bool, ::Neutral{ 1}) = !x
impl_xor(x::Bool, ::Neutral{-1}) = !x

#------------------------------------------------------------------------------ Bit shifts -

# In Julia, the type of `x << y`, `x >> y`, and `x >>> y` is determined by `x` not by `y`:
# the result is an `Int` if `x` is a Boolean and the result has the same type as `x`
# otherwise.
#
# In Julia implementation, the direction of shift is reversed if `y` is negative, so that
# the number of bits to shift can be specified as an `UInt`. We do the same here when `y` is
# a neutral number.

"""
    Neutrals.impl_lshft(x, y) -> x << y

Implement left bit shift of integer `x` by neutral number `y`.

"""
function impl_lshft(x::Integer, y::Neutral)
    if iszero(y) # x << 𝟘
        return lshft0(x)
    elseif isone(y) # x << 𝟙
        return lshft1(x)
    else # x << -𝟙 -> x >> 𝟙
        return rshft1(x)
    end
end

function impl_lshft(x::Neutral, y::Integer)::Int
    iszero(x) && return 0
    if !(y isa Bool)
        return Int(x) << y
    elseif isone(x) # 𝟙 << y
        return y ? 2 : 1
    else # -𝟙 << y
        return ifelse(y, (-1) << 1, -1)
    end
end

"""
    Neutrals.impl_rshft(x, y) -> x >> y

Implement right bit shift of integer `x` by neutral number `y`.

"""
function impl_rshft(x::Integer, y::Neutral)
    if iszero(y) # x >> 𝟘
        return rshft0(x)
    elseif isone(y) # x >> 𝟙
        return rshft1(x)
    else # x >> -𝟙 -> x << 𝟙
        return lshft1(x)
    end
end

function impl_rshft(x::Neutral, y::Integer)::Int
    iszero(x) && return 0
    if !(y isa Bool)
        return Int(x) >> y
    elseif isone(x) # 𝟙 >> y
        return y ? 0 : 1
    else # -𝟙 << y
        return ifelse(y, (-1) >> 1, -1) # FIXME both values are -1
    end
end

"""
    Neutrals.impl_urshft(x, y) -> x >>> y

Implement unsigned right bit shift of integer `x` by neutral number `y`.

"""
function impl_urshft(x::Integer, y::Neutral)
    if iszero(y) # x >>> 𝟘
        return urshft0(x)
    elseif isone(y) # x >>> 𝟙
        return urshft1(x)
    else # x >>> -𝟙 -> x << 𝟙
        return lshft1(x)
    end
end

function impl_urshft(x::Neutral, y::Integer)::Int
    iszero(x) && return 0
    if !(y isa Bool)
        return Int(x) >>> y
    elseif isone(x) # 𝟙 >>> y
        return y ? 0 : 1
    else # -𝟙 >>> y
        return ifelse(y, (-1) >>> 1, -1)
    end
end

# Helper functions to unify bit-shifting code for integers and Booleans.
#
# x << 0
lshft0(x::Integer) = x
lshft0(x::Bool) = x ? 1 : 0 # convert x to Int
#
# x << 1
lshft1(x::Integer) = x << UInt(1)
lshft1(x::Bool) = x ? 2 : 0
#
# x >> 0 (same as x << 0)
rshft0(x::Integer) = lshft0(x)
#
# x >> 1
rshft1(x::Integer) = x >> UInt(1)
rshft1(x::Bool) = 0
#
# x >>> 0 (same as x >> 0)
urshft0(x::Integer) = rshft0(x)
#
# x >>> 1
urshft1(x::Integer) = x >>> UInt(1)
urshft1(x::Bool) = 0

#----------------------------------------------------------------------------- Big numbers -
#
# FIXME Not needed anymore. Remove.
#
# As can be seen in `base/gmp.jl` and `base/mpfr.jl`, the result of a comparison with `==`,
# `<`, or `<=` between a big number and a non-big number is given by `cmp`. So there are no
# needs to specialize `==`, `<`, and `<=` to handle these cases, only `cmp` may be
# specialized. For big floats, `cmp` converts the non-big operand to a big float so there
# nothing to do here. For big integers, `cmp` with a non-big integer `c` of size not larger
# than a `Clong` calls one of the compiled methods with `c` as a `Clong` or as a `Culong`.
# Hence, we only have to specialize `cmp` for a big integer and a neutral number.
impl_cmp(x::BigInt, y::Neutral{ 0}) = cmp(x, Culong(0))
impl_cmp(x::BigInt, y::Neutral{ 1}) = cmp(x, Culong(1))
impl_cmp(x::BigInt, y::Neutral{-1}) = cmp(x, Clong(-1))
#
# As can be seen in `base/gmp.jl`, for the addition or subtraction of a big integer with
# `c`, an integer of size ≤ `sizeof(Clong)`, the operation branches on the sign of `c` to
# call one of the compiled methods with `c` or `-c` converted to `Culong`. For a neutral
# number `c`, this test is decidable at compile time, and we want to convert the operation
# is an equivalent one involving `c` or `-c` converted to a `Culong`.
#
# As can be seen in `base/mpfr.jl`, for the addition or subtraction of a big float with `c`,
# an integer of size ≤ `sizeof(Clong)`, the operation calls one of the compiled methods with
# `c` a `Clong` or a `Culong`. Benchmarking shows no real differences between the two so, in
# order to make the code similar as the one for big integers, we manage to convert `c` or
# `-c` to a `Culong`.
for T in (:BigInt, :BigFloat)
    @eval begin
        # Addition. It is only needed to extend the rules for `±𝟙`.
        impl_add(x::$T, y::Neutral{ 1}) = x + Culong(1)
        impl_add(x::$T, y::Neutral{-1}) = x - Culong(1)

        # Subtraction. It is only needed to extend the rules for `±𝟙`.
        impl_sub(x::$T, y::Neutral{ 1}) = x - Culong(1)
        impl_sub(x::$T, y::Neutral{-1}) = x + Culong(1)

        impl_sub(x::Neutral{ 1}, y::$T) = Culong(1) - y
        impl_sub(x::Neutral{-1}, y::$T) = -(y + Culong(1))

        # Equality. It is only needed to extend the rules for `-𝟙`.
        impl_eq(x::$T, y::Neutral{-1}) = x == Clong(-1)
    end
end

#------------------------------------------------------------------------- Complex numbers -
# Specific rules for complex numbers.

# Extend `Complex(x,y)` to behave as `x + y*im` when at least one of `x` or `y` is a
# neutral number. (The 3rd rule is needed to remove any ambiguities.)
Base.Complex(x::Neutral{0}, y::Real      ) = y*im # 𝟘 + y*im -> y*im
Base.Complex(x::Real,       y::Neutral{0}) = x    # x + 𝟘*im -> x
Base.Complex(x::Neutral{0}, y::Neutral{0}) = ZERO # 𝟘 + 𝟘*im -> 𝟘

# For the left division between a complex number and a neutral number, we want to avoid
# calling the adjoint method which would convert a Complex{Bool} into a Complex{Int}).
Base.:(\)(x::Neutral, y::Complex) = y/x
Base.:(\)(x::Complex, y::Neutral) = y/x
