"""

Package `Neutrals` provides two constants `ZERO` and `ONE` which are neutral elements for
respectively the addition and the multiplication of numbers. In other words, whatever the
type and the value of the number `x`, `x + ZERO` and `ONE*x` yield `x` unchanged. In
addition, `ZERO` is a *strong zero* in the sense that `ZERO*x` yields `ZERO` even though
`x` may be `±Inf` or `±NaN`.

"""
module Neutrals

export Neutral, ZERO, ONE

using TypeUtils
using TypeUtils: @public

@public value
@public impl_add impl_sub impl_mul impl_div impl_pow
@public impl_eq impl_lt impl_le impl_cmp
@public impl_trd impl_rem impl_mod
@public impl_lshft impl_rshft impl_urshft
@public impl_or impl_and impl_xor
@public is_dimensionless

if !isdefined(Base, :get_extension)
    using Requires
end

"""
    Neutral{V}()
    Neutral(V)

yield a neutral number of value `V` (one of `0`, `1`, or `-1`) which implement the
following properties:

* `Neutral(0)` is the neutral element for the addition of dimensionless numbers and is a
  *strong zero* for the multiplication of numbers.

* `Neutral(1)` is the neutral element for the multiplication of numbers. Conversion of
  `Neutral(1)` to type `T` yields `one(T)`.

* Multiplying by `Neutral(-1)` always negate the other operand. Conversion of
  `Neutral(-1)` to type `T` yields `-one(T)`.

Instances of `Neutral` are singletons whose value and behavior are known at compile time.
This may trigger valuable optimizations.

Exported symbols [`ZERO`](@ref) and `𝟘` are aliases for `Neutral(0)` while [`ONE`](@ref)
and `𝟙` are aliases for `Neutral(1)`. Expressions `-ONE` and `-𝟙` are compiled as
`Neutral(-1)`.

"""
struct Neutral{V} <: Integer
    # Inner constructors to purposely limit the set of neutral numbers.
    Neutral{0}() = new{0}()
    Neutral{1}() = new{1}()
    Neutral{-1}() = new{-1}() # Neutral(-1) is needed for arithmetic.
end

"""
    Neutrals.value(x)
    Neutrals.value(typeof(x))

yield the value associated with neutral number `x`.

"""
value(::Neutral{x}) where x = x
value(::Type{Neutral{x}}) where x = x

# For numbers, there is no needs to extend `Base.convert` with the following "conversion"
# constructors as `Base.convert(T, x)` falls back to call `T(x)::T`.
Neutral(x::Neutral) = x
Neutral(x::Number) = Neutral(Int(x)::Int)
Neutral(x::Int) = Neutral{x}()
Neutral{V}(x::Neutral{V}) where {V} = x
Neutral{V}(x::Neutral) where {V} = throw(InexactError(:convert, Neutral{V}, x))
Neutral{V}(x::Number) where {V} = x == V ? Neutral{V}() : throw(InexactError(:convert, Neutral{V}, x))

# Error catcher.
Neutral{V}() where {V} = throw(ArgumentError(
    "value "*(V isa Number ? repr(V) : "of type `$(typeof(V))`")
    *" cannot be converted into a neutral number"))

"""
    ZERO
    𝟘    # for Julia ≤ 1.3

is a singleton representing a strong neutral element for the addition of numbers whose
effect is to leave the other operand unchanged in an addition. More specifically, whatever
the type of the number `x`, the following rules are implemented:

    x + ZERO -> x          x - ZERO -> x
    ZERO + x -> x          ZERO - x -> -x # i.e., negate x

When the above result is `x`, it means that the very same object is returned, e.g. `ZERO +
x === x` holds. This is important if `x` is not an instance of an `isbitstype` type like
`BigInt` or `BigFloat`.

For consistency, with [`ONE`](@ref) or `𝟙`, the neutral element for the multiplication,
the following rules are implemented for the multiplication and the division:

    x*ZERO -> ZERO                ZERO*x -> ZERO
    ZERO/x -> ZERO

The type of `ZERO`, given by `typeof(ZERO)` or [`Neutral{0}`](@ref Neutral), is unique and
is a sub-type of `Real`.

"""
const ZERO = Neutral(0)

"""
    ONE
    𝟙    # for Julia ≤ 1.3

yield a singleton representing the neutral element for the multiplication of numbers of
any type. In other words and whatever the type of the number `x`, the expression `𝟙*x`
yields `x` unchanged.

effect is to leave the other operand unchanged in a multiplication. More specifically,
whatever the type of the number `x`, the following rules are implemented:

    ONE*x -> x            x/ONE -> x           ONE/x -> inv(x)
    x*ONE -> x            ONE\\x -> x           x\\ONE -> inv(x)

When the above result is `x`, it means that the very same object is returned, e.g. `ONE*x
=== x` holds. This is important if `x` is not an instance of an `isbitstype` type like
`BigInt` or `BigFloat`.

`ONE` can be used in comparisons:

    x == ONE -> isone(x)          isequal(x, ONE) -> isone(x)
    ONE == x -> isone(x)          isequal(ONE, x) -> isone(x)

`-ONE`, the opposite of `ONE`, is also a singleton which may be used to represent a value
whose inferable effect is to negate the other operand. Multiplications and divisions with
`-ONE` follow the rules:

    (-ONE)*x -> -x        x/(-ONE) -> -x        (-ONE)/x -> -inv(x)
    x*(-ONE) -> -x        (-ONE)\\x -> -x        x\\(-ONE) -> -inv(x)

Compared to numerical values equal to `±1`, `ONE` and `-ONE` are singletons whose types
are unique and whose effects are known at compile time which opens possibilities to
optimize the code.

For consistency, with [`ZERO`](@ref) or `𝟘`, the neutral element for the addition of numbers, the
following rules are implemented for the addition and subtraction:

    ONE - ONE -> ZERO
    ONE + (-ONE) -> ZERO
    etc.

The types of `ONE` and `-ONE`, given by `typeof(ONE)` and `typeof(-ONE)` or by
[`Neutral{1}`](@ref Neutral) and [`Neutral{-1}`](@ref Neutral), are both unique and are
sub-types of `Integer`.

"""
const ONE = Neutral(1)

# Using `𝟘` and `𝟙` as names of constants is only supported for Julia ≥ 1.3.
VERSION ≥ v"1.3" && eval(Meta.parse("export 𝟘, 𝟙; const 𝟘 = ZERO; @doc (@doc ZERO) 𝟘; const 𝟙 = ONE; #=@doc ONE 𝟙;=#"))

@eval Base.instances(::Type{Neutral}) = $(map(Neutral, (0, 1, -1)))

# Aliases to encode rules. `AnyNeutral` is more specific than `Neutral` and is a union of
# concrete types.
const AnyNeutral = Union{map(typeof, instances(Neutral))...}
const NonZeroNeutral = Union{Neutral{1},Neutral{-1}}
const NonNegativeNeutral = Union{Neutral{0},Neutral{1}}
const BigNumber = Union{BigInt,BigFloat}

# `BareNumbers` are dimensionless.
const BareNumber = Union{Real,Complex}

Base.typemin(::Type{Neutral}) = -ONE
Base.typemin(::Type{Neutral{x}}) where {x} = Neutral{x}()
Base.typemax(::Type{Neutral}) = ONE
Base.typemax(::Type{Neutral{x}}) where {x} = Neutral{x}()

TypeUtils.is_signed(::Type{<:Neutral}) = true

for (T, name, descr) in ((Neutral{0}, "𝟘",
                          "neutral element for the addition of numbers"),
                         (Neutral{1}, "𝟙",
                          "neutral element for the multiplication of numbers"),
                         (Neutral{-1}, "-𝟙",
                          "opposite of neutral element for the multiplication of numbers"))
    mesg = name * " (" * descr * ")"
    @eval begin
        Base.show(io::IO, ::$T) = print(io, $name)
        #Base.show(io::IO, ::MIME"text/plain", ::$T) = print(io, $mesg)
        Base.summary(io::IO, ::$T) = print(io, $mesg)
    end
end

# Conversion rules for bare numeric types. No needs to directly extend `Base.convert`
# which calls `T(x)` for numbers except for Booleans.
for T in (Bool,
          Int8, Int16, Int32, Int64, Int128, BigInt,
          UInt8, UInt16, UInt32, UInt64, UInt128,
          Float16, Float32, Float64, BigFloat)
    @eval (::Type{$T})(x::Neutral) = $T(value(x))
    if !is_signed(T)
        @eval (::Type{$T})(x::Neutral{-1}) = throw(InexactError(:convert, $T, x))
    end
end
(::Type{Rational{T}})(x::Neutral) where {T<:Integer} = Rational(T(x))
(::Type{Rational})(x::Neutral) = Rational(value(x), 1)
(::Type{Complex{T}})(x::Neutral) where {T<:Real} = Complex(T(x), T(0))
(::Type{Complex})(x::Neutral) = Complex(value(x), 0)
(::Type{AbstractFloat})(x::Neutral) = float(value(x))
Base.convert(::Type{Bool}, x::Neutral{ 0}) = false
Base.convert(::Type{Bool}, x::Neutral{ 1}) = true
Base.convert(::Type{Bool}, x::Neutral{-1}) = throw(InexactError(:convert, Bool, -ONE))


# Conversion rules for any other numeric type `T` and assuming efficient implementations
# of `zero(T)` and `one(T)`
Base.convert(::Type{Integer}, x::Neutral) = x
Base.convert(::Type{T}, x::Neutral) where {T<:BareNumber} = impl_conv(T, x)
Base.convert(::Type{T}, x::Neutral) where {T<:Number} =
    is_dimensionless(T) ? impl_conv(T, x) : throw_convert_neutral_to_dimensionful_type(T, x)

impl_conv(::Type{T}, x::Neutral{0}) where {T<:Number} = zero(T)
impl_conv(::Type{T}, x::Neutral{1}) where {T<:Number} = one(T)
impl_conv(::Type{T}, x::Neutral{-1}) where {T<:Number} = -one(T)
impl_conv(::Type{T}, x::Neutral{-1}) where {T<:Union{Bool,Unsigned,Rational{<:Union{Bool,Unsigned}},Complex{<:Union{Bool,Unsigned}}}} =
    throw(InexactError(:convert, T, x))

@noinline throw_convert_neutral_to_dimensionful_type(::Type{T}, x::Neutral) where {T} =
    throw(ArgumentError("cannot convert $x to dimensionful type $T"))

# Extend unary `-` for neutral numbers. Unary `+`, `*`, `&`, `|`, and `xor` do not need to
# be extended for numbers (see base/operators.jl).
Base.:(-)(x::Neutral{0}) = ZERO
Base.:(-)(x::Neutral{1}) = Neutral{-1}() # NOTE do not use expression `-ONE` here
Base.:(-)(x::Neutral{-1}) = ONE

# Bitwise not. Yield an `Int` if result cannot be represented by a neutral number.
Base.:(~)(x::Neutral{0}) = -ONE
Base.:(~)(x::Neutral{-1}) = ZERO
Base.:(~)(::Neutral{x}) where {x} = ~x

# Extend unary functions for neutral numbers (following order in base/number.jl).
Base.iszero(x::Neutral) = false
Base.iszero(x::Neutral{0}) = true
#
Base.isone(x::Neutral) = false
Base.isone(x::Neutral{1}) = true
#
Base.isfinite(x::Neutral) = true
#
Base.sign(x::Union{Neutral{0},Neutral{1},Neutral{-1}}) = value(x)
#
Base.signbit(x::NonNegativeNeutral) = false
Base.signbit(x::Neutral) = true
#
for f in (:abs, :abs2)
    @eval begin
        Base.$f(x::NonNegativeNeutral) = x
        Base.$f(x::Neutral{-1}) = ONE
    end
end
#
Base.angle(::NonNegativeNeutral) = ZERO
Base.angle(::Neutral) = π
#
Base.inv(x::Neutral{0}) = throw(DivideError())
Base.inv(x::Union{Neutral{1},Neutral{-1}}) = x
#
Base.zero(::Neutral) = ZERO
Base.zero(::Type{<:Neutral}) = ZERO
#
Base.one(::Neutral) = ONE
Base.one(::Type{<:Neutral}) = ONE
#
Base.isodd(::Neutral{x}) where {x} = isodd(x)
Base.iseven(::Neutral{x}) where {x} = iseven(x)

# For integers, `Base.rem(x, T)` may be used to "convert" `x` to type `T`.
Base.rem(x::Neutral, ::Type{Integer}) = x
Base.rem(::Neutral{x}, ::Type{T}) where {x,T<:Integer} = x % T
for T in (:Bool, :BigInt) # remove ambiguities for these types
    @eval Base.rem(::Neutral{x}, ::Type{$T}) where {x} = x % $T
end

# Extend `Base.promote_rule` when one of the argument is a neutral number. For two neutral
# numbers, the default is to convert them to `Int`. For `Bool`, the symmetric promote rule
# must be given to avoid overflows.
Base.promote_rule(::Type{<:Neutral}, ::Type{<:Neutral}) = Int
Base.promote_rule(::Type{<:Neutral}, ::Type{T}) where {T<:Number} = T
Base.promote_rule(::Type{Bool}, ::Type{<:Neutral}) = Bool
Base.promote_rule(::Type{Bool}, ::Type{Neutral{-1}}) = Int
Base.promote_rule(::Type{Neutral{-1}}, ::Type{Bool}) = Int

# For some binary operations involving neutral numbers, it is sufficient to apply the base
# method for the arguments promoted according to promotion rules. Other operations must be
# specialized either because the operation has a specific "hard-coded" result (e.g. `𝟙*x
# -> x` or `x + 𝟘 -> x`) or because the promotion rules are inappropriate. In this
# package, such base methods are extended when at least one the operand is a neutral
# number (without specializing on the specific value of the neutral operand, hence, for
# type `Neutral` in the signature of the method) to call an implementation of the
# operation named `Neutrals.impl_$op` where `$op` is the name of the operation (e.g.,
# `add` for `+`). Methods implementing binary operations are public but not exported and
# can be specialized for specific values of the neutral argument and/or type of the other
# argument. Implementations of binary operations when both arguments are neutral number
# are automatically encoded when the package is built.
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
# and similarly for `-`, for comparing numbers:
#
#     ==(x::Number, y::Number) in `basae/promotion.jl`
#     <( x::Real, y::Real)     in `basae/promotion.jl`
#     <=(x::Real, y::Real)     in `basae/promotion.jl`
#
# Override base methods to call corresponding implementation:
for (f, (g, w, Ts)) in (:(+)   => (:impl_add,    3, (:Integer, :Rational, :AbstractIrrational,
                                                     :AbstractFloat, :BigInt, :BigFloat)),
                        :(-)   => (:impl_sub,    3, (:Integer, :Rational, :AbstractIrrational,
                                                     :AbstractFloat, :BigInt, :BigFloat)),
                        :(*)   => (:impl_mul,    3, (:Number, :Integer, :Rational)),
                        :(/)   => (:impl_div,    3, (:Number, :Integer, :Rational)),
                        :(^)   => (:impl_pow,    2, (:Number, :Rational, :BigInt,
                                                     :Float16, :Float32, :Float64, :BigFloat,
                                                     :Complex, :(Complex{<:AbstractFloat}))),
                        :div   => (:impl_trd,    3, (:Integer,)),
                        :rem   => (:impl_rem,    3, (:Integer,)),
                        :mod   => (:impl_mod,    3, (:Integer,)),
                        :(==)  => (:impl_eq,     3, (:Number, :Rational, :BigInt, :BigFloat)),
                        :(<)   => (:impl_lt,     3, (:Real, :Rational)),
                        :(<=)  => (:impl_le,     3, (:Real, :Rational)),
                        :cmp   => (:impl_cmp,    3, (:Number, :Integer, :BigInt, :BigFloat)),
                        :(|)   => (:impl_or,     3, (:Integer,)),
                        :(&)   => (:impl_and,    3, (:Integer,)),
                        :xor   => (:impl_xor,    3, (:Integer,)),
                        :(<<)  => (:impl_lshft,  2, (:Integer,)),
                        :(>>)  => (:impl_rshft,  2, (:Integer,)),
                        :(>>>) => (:impl_urshft, 2, (:Integer,)),
                        )
    @eval Base.$f(x::Neutral, y::Neutral) = $g(x, y)
    for T in Ts
        if (w & 1) != 0
            @eval Base.$f(x::Neutral, y::$T) = $g(x, y)
        end
        if (w & 2) != 0
            @eval Base.$f(x::$T, y::Neutral) = $g(x, y)
        end
    end
end

# Encode implementation of some binary operators/functions when both operands are neutral
# numbers. For other binary operators/functions, the base methods are assumed to work
# thanks to the implemented promotion rules.
for x in instances(Neutral), y in instances(Neutral)
    for (f, g) in (:(+)   => :impl_add,
                   :(-)   => :impl_sub,
                   :(*)   => :impl_mul,
                   :(==)  => :impl_eq,
                   :(<)   => :impl_lt,
                   :(<=)  => :impl_le,
                   :(|)   => :impl_or,
                   :(&)   => :impl_and,
                   :(xor) => :impl_xor,
                   :(<<)  => :impl_lshft,
                   :(>>)  => :impl_rshft,
                   :(>>>) => :impl_urshft)
        r = @eval $f(value($x), value($y))
        if r isa Bool
            @eval $g(::$(typeof(x)), ::$(typeof(y))) = $r
        elseif r ∈ (0, 1, -1) # returns a neutral number if possible
            @eval $g(::$(typeof(x)), ::$(typeof(y))) = $(Neutral{r}())
        else # otherwise returns an integer
            @eval $g(::$(typeof(x)), ::$(typeof(y))) = $r
        end
    end

    # Division, modulo, etc.
    for (f, g) in (:(/) => :impl_div,
                   :div => :impl_trd,
                   :rem => :impl_rem,
                   :mod => :impl_mod)
        if y === ZERO
            @eval $g(::$(typeof(x)), ::$(typeof(y))) = throw(DivideError())
        else # y is ONE or -ONE
            r = if f === :(/)
                value(x)*value(y) # x/y yields the same result as x*y when abs(y) = 1
            else
                @eval $f(value($x), value($y))
            end
            @eval $g(::$(typeof(x)), ::$(typeof(y))) = $(Neutral{r}())
        end
    end

    # Exponentiation.
    @eval impl_pow(::$(typeof(x)), ::$(typeof(y))) = $(y === ZERO ? ONE : x)

    # Comparison.
    @eval impl_cmp(::$(typeof(x)), ::$(typeof(y))) = $(cmp(value(x), value(y)))
end

"""
    Neutrals.impl_add(x, y) -> x + y

implements addition of numbers `x` and `y` when at least one of the operands is a neutral
number.

This method can be overridden by specializing it when the second operand is a neutral
number.

"""
impl_add(x::Neutral, y::Number) = impl_add(y, x) # put neutral number second
impl_add(x::BareNumber, ::Neutral{0}) = x
impl_add(x::Number, ::Neutral{ 0}) = is_dimensionless(x) ? x : throw_add_dimensionful_and_zero()
impl_add(x::Number, ::Neutral{ 1}) = x + one(x)
impl_add(x::Number, ::Neutral{-1}) = x - one(x)

@noinline throw_add_dimensionful_and_zero() =
    throw(ArgumentError("𝟘 and dimensionful quantity cannot be added"))

"""
    Neutrals.impl_sub(x, y) -> x - y

implements subtraction of numbers `x` and `y` when at least one of the operands is a
neutral number.

"""
impl_sub(x::BareNumber, ::Neutral{0}) = x
impl_sub(x::Number, ::Neutral{ 0}) = is_dimensionless(x) ? x : throw_sub_dimensionful_and_zero()
impl_sub(x::Number, ::Neutral{ 1}) = x - one(x)
impl_sub(x::Number, ::Neutral{-1}) = x + one(x)

impl_sub(::Neutral{ 0}, x::BareNumber) = -x
impl_sub(::Neutral{ 0}, x::Number) = is_dimensionless(x) ? -x : throw_sub_dimensionful_and_zero()
impl_sub(::Neutral{ 1}, x::Number) = one(x) - x
impl_sub(::Neutral{-1}, x::Number) = -one(x) - x

@noinline throw_sub_dimensionful_and_zero() =
    throw(ArgumentError("𝟘 and dimensionful quantity cannot be subtracted"))

# In Julia, Booleans are promoted to `Int` for addition, subtraction and bitwise shifts
# (base/bool.jl). The implementations of addition and subtraction of a Boolean with `±𝟙`
# are specialized according to this.
impl_add(x::Bool, y::Neutral{ 1}) = Int(x) + 1
impl_add(x::Bool, y::Neutral{-1}) = Int(x) - 1
#
impl_sub(x::Bool, ::Neutral{ 1}) = Int(x) - 1
impl_sub(x::Bool, ::Neutral{-1}) = Int(x) + 1
impl_sub(::Neutral{ 1}, x::Bool) = 1 - Int(x)
impl_sub(::Neutral{-1}, x::Bool) = -1 - Int(x)

"""
    Neutrals.impl_mul(x, y) -> x*y

implements multiplication of number `x` by number `y` when at least one of the operands is a
neutral number.

This method can be overridden by specializing it when the first operand is a neutral
number.

"""
impl_mul(x::Number, y::Neutral) = impl_mul(y, x) # put neutral number first
impl_mul(::Neutral{ 0}, x::BareNumber) = ZERO
impl_mul(::Neutral{ 1}, x::Number) = x
impl_mul(::Neutral{-1}, x::Number) = -x

"""
    Neutrals.impl_div(x, y) -> x / y

implements division of number `x` by number `y` when at least one of the operands is a
neutral number.

"""
impl_div(x::Number, ::Neutral{ 0}) = throw(DivideError())
impl_div(x::Number, ::Neutral{ 1}) = x
impl_div(x::Number, ::Neutral{-1}) = -x

impl_div(::Neutral{ 0}, x::BareNumber) = ZERO
impl_div(::Neutral{ 1}, x::Number) = inv(x)
impl_div(::Neutral{-1}, x::Number) = -inv(x)

"""
    Neutrals.impl_trd(x, y) -> x ÷ y

implements the truncated division of `x` by `y` that is the quotient of `x` by `y` rounded
toward zero. This corresponds to `div(x,y,RoundToZero)`.

"""
impl_trd(x::Real, y::Neutral{0}) = throw(DivideError())
impl_trd(x::Real, y::Neutral) = x ÷ value(y)
impl_trd(x::Neutral, y::Real) = value(x) ÷ x

# Specialize for integers and for `±𝟙`.
impl_trd(x::Integer, y::Neutral{1}) = x
impl_trd(x::Integer, y::Neutral{-1}) = -x

"""
    Neutrals.impl_rem(x, y) -> rem(x, y)

implements the remainder function when at least one of the operands is a neutral number.

The remainder function satisfies `x == div(x,y)*y + rem(x,y)` with `div` the truncated
division which yields the quotient rounded toward zero, implying that sign matches `x`.

"""
impl_rem(x::Real, y::Neutral{0}) = throw(DivideError())
impl_rem(x::Real, y::Neutral) = rem(x, oftype(x, value(y)))
impl_rem(x::Neutral, y::Real) = rem(oftype(y, value(x)), y)

# Specialize implementation for integers and for `±𝟙`. For Booleans, the following rules
# for integers amount to assuming that the result does not depend on the sign of the right
# operand.
impl_rem(x::Integer, y::Neutral{1}) = zero(x)
impl_rem(x::Integer, y::Neutral{-1}) = zero(x)

"""
    Neutrals.impl_mod(x, y) -> mod(x, y)

implements `mod` when at least one of the operands is a neutral number.

The modulus function satisfies `x == fld(x,y)*y + mod(x,y)`, with `fld` the floored
division which yields the rounded towards `-Inf`, implying that sign matches `y`.

"""
impl_mod(x::Real, y::Neutral{0}) = throw(DivideError())
impl_mod(x::Real, y::Neutral) = mod(x, oftype(x, value(y)))
impl_mod(x::Neutral, y::Real) = mod(oftype(y, value(x)), y)

# Specialize implementation for integers and for `±𝟙`. For Booleans, the following rules
# for integers amount to assuming that the result does not depend on the sign of the right
# operand.
impl_mod(x::Integer, y::Neutral{1}) = zero(x)
impl_mod(x::Integer, y::Neutral{-1}) = zero(x)

"""
    Neutrals.impl_pow(x, y) -> x^y

implements raising number `x` to the power `y` when `y` is a neutral number.

"""
impl_pow(x::Number, ::Neutral{0}) = oneunit(x)
impl_pow(x::Number, ::Neutral{1}) = x
impl_pow(x::Number, ::Neutral{-1}) = inv(x)

# There is no `oneunit` for irrational numbers.
impl_pow(x::Irrational, ::Neutral{0}) = 1.0

"""
    Neutrals.impl_eq(x, y) -> x == y

implements `==` for numbers when at least one of the operands is a neutral number.

This method can be overridden by specializing it when the second operand is a neutral
number.

"""
impl_eq(x::Neutral, y::Number) = impl_eq(y, x) # put neutral number second
impl_eq(x::Number, ::Neutral{ 0}) = is_dimensionless(x) && iszero(x)
impl_eq(x::Number, ::Neutral{ 1}) = isone(x)
impl_eq(x::Number, ::Neutral{-1}) = x == -one(x)

"""
    Neutrals.impl_lt(x, y) -> x < y

implements `<` for real numbers when at least one of the operands is a neutral number.

"""
impl_lt(x::Real, y::Neutral{ 0}) = x < zero(x)
impl_lt(x::Real, y::Neutral{ 1}) = x <  one(x)
impl_lt(x::Real, y::Neutral{-1}) = x < -one(x)

impl_lt(x::Neutral{ 0}, y::Real) = zero(y) < y
impl_lt(x::Neutral{ 1}, y::Real) =  one(y) < y
impl_lt(x::Neutral{-1}, y::Real) = -one(y) < y

"""
    Neutrals.impl_le(x, y) -> x ≤ y

implements `≤` for real numbers when at least one of the operands is a neutral number.

"""
impl_le(x::Real, y::Neutral{ 0}) = x <= zero(x)
impl_le(x::Real, y::Neutral{ 1}) = x <=  one(x)
impl_le(x::Real, y::Neutral{-1}) = x <= -one(x)

impl_le(x::Neutral{ 0}, y::Real) = zero(y) <= y
impl_le(x::Neutral{ 1}, y::Real) =  one(y) <= y
impl_le(x::Neutral{-1}, y::Real) = -one(y) <= y

"""
    Neutrals.impl_cmp(x, y) -> cmp(x, y)

implements `cmp` for real numbers when at least one of the operands is a neutral number.

This method can be overridden by specializing it when the second operand is a neutral
number.

"""
impl_cmp(x::Neutral, y::Real) = -impl_cmp(y, x) # put neutral number second
impl_cmp(x::Real, y::Neutral) = cmp(x, oftype(x, value(y)))

# Specialize methods implementing comparisons for cases involving an unsigned real and, at
# least, `-𝟙` which cannot be converted to an unsigned real.
for T in (Bool, Unsigned, Rational{<:Union{Bool,Unsigned}})
    @eval begin
        impl_eq(x::$T, y::Neutral{-1}) = false
        #
        impl_lt(x::$T, y::Neutral{0}) = false
        impl_lt(x::$T, y::Neutral{-1}) = false
        impl_lt(x::Neutral{-1}, y::$T) = true
        #
        impl_le(x::$T, y::Neutral{-1}) = false
        impl_le(x::Neutral{0}, y::$T) = true
        impl_le(x::Neutral{-1}, y::$T) = true
        #
        impl_cmp(x::$T, y::Neutral{-1}) = 1
        impl_cmp(x::$T, y::Neutral{0}) = iszero(x) ? 0 : 1
    end
end

# When neutral operand is not `-𝟙` (this case is considered elsewhere for unsigned reals),
# avoid promotion for comparison a Boolean and a neutral number.
impl_eq(x::Bool, y::Neutral{1}) = x
impl_eq(x::Bool, y::Neutral{0}) = !x
#
impl_lt(x::Bool, y::Neutral{1}) = !x
impl_lt(x::Neutral{0}, y::Bool) = y
impl_lt(x::Neutral{1}, y::Bool) = false
#
impl_le(x::Bool, y::Neutral{0}) = !x
impl_le(x::Bool, y::Neutral{1}) = true
impl_le(x::Neutral{1}, y::Bool) = y
#
impl_cmp(x::Bool, y::Neutral{1}) = x ? 0 : -1

# For bitwise operations (`|`, `&`, and `xor`) between integers (including Booleans and
# big integers) of mixed types, the called methods are defined in `base/int.jl` and
# promote their arguments before calling a more specialized method. When one operand is a
# neutral number, we override this method to implement optimized expressions. Even though
# the other operand is unsigned, we consider that `-𝟙` behaves as a constant of the same
# type with all its bits set to 1.

"""
    Neutrals.impl_or(x, y)

yields `x | y` when one of the operands is a neutral number while the other is an integer.
If this method is overridden, it is sufficient to specialize it when the second operand is
a neutral number.

"""
impl_or(x::Neutral, y::Integer) = impl_or(y, x) # put neutral neutral second
impl_or(x::Integer, ::Neutral{0}) = x
impl_or(x::Integer, ::Neutral{1}) = x | one(x)
impl_or(x::Integer, ::Neutral{-1}) = -one(x)

"""
    Neutrals.impl_and(x, y)

yields `x & y` when one of the operands is a neutral number while the other is an integer.
If this method is overridden, it is sufficient to specialize it when the second operand is
a neutral number.

"""
impl_and(x::Neutral, y::Integer) = impl_and(y, x) # operation is commutative
impl_and(x::Integer, ::Neutral{0}) = zero(x)
impl_and(x::Integer, ::Neutral{1}) = x & one(x)
impl_and(x::Integer, ::Neutral{-1}) = x

"""
    Neutrals.impl_xor(x, y)

yields `xor(x, y)` when one of the operands is a neutral number while the other is an
integer. If this method is overridden, it is sufficient to specialize it when the second
operand is a neutral number.

"""
impl_xor(x::Neutral, y::Integer) = impl_xor(y, x) # operation is commutative
impl_xor(x::Integer, ::Neutral{0}) = x
impl_xor(x::Integer, ::Neutral{1}) = xor(x, one(x))
impl_xor(x::Integer, ::Neutral{-1}) = xor(x, -one(x))

# For bitwise operations with Booleans, `±𝟙` is seen as `true`.
impl_or(x::Bool, ::Neutral{1}) = true
impl_or(x::Bool, ::Neutral{-1}) = true
#
impl_and(x::Bool, ::Neutral{1}) = x
impl_and(x::Bool, ::Neutral{-1}) = x
#
impl_xor(x::Bool, ::Neutral{1}) = !x
impl_xor(x::Bool, ::Neutral{-1}) = !x

# For bit shift operation of an integer `x` (including Booleans and big integers) by a
# number of bits specified by a neutral number, it is sufficient to override the
# corresponding base methods (in `base/operators.jl`) whose left operand is an `Integer`
# and the right one is an `Int` to yield either `x` (if shifting by 𝟘) or to call the
# right operation with a number of bits specified as an `UInt` (see base/int.jl).

"""
    Neutrals.impl_lshft(x, y) -> x << y

yields left bit shift of integer `x` by neutral number `y`.

"""
impl_lshft(x::Integer, ::Neutral{ 0}) = x
impl_lshft(x::Integer, ::Neutral{ 1}) = x << UInt(1)
impl_lshft(x::Integer, ::Neutral{-1}) = x >> UInt(1)

"""
    Neutrals.impl_rshft(x, y) -> x >> y

yields right bit shift of integer `x` by neutral number `y`.

"""
impl_rshft(x::Integer, ::Neutral{ 0}) = x
impl_rshft(x::Integer, ::Neutral{ 1}) = x >> UInt(1)
impl_rshft(x::Integer, ::Neutral{-1}) = x << UInt(1)

"""
    Neutrals.impl_rshft(x, y) -> x >>> y

yields unsigned right bit shift of integer `x` by neutral number `y`.

"""
impl_urshft(x::Integer, ::Neutral{ 0}) = x
impl_urshft(x::Integer, ::Neutral{ 1}) = x >>> UInt(1)
impl_urshft(x::Integer, ::Neutral{-1}) = x << UInt(1)

"""
    Neutrals.is_dimensionless(x)
    Neutrals.is_dimensionless(typeof(x))

yields whether number `x` is dimensionless.

"""
is_dimensionless(x::Number) = is_dimensionless(typeof(x))
is_dimensionless(::Type{<:BareNumber}) = true

#-----------------------------------------------------------------------------------------
# BIG NUMBERS
#
# As can be seen in `base/gmp.jl` and `base/mpfr.jl`, for `==`, `<`, and `<=` with a big
# number and a non-big number, the result is given by `cmp`. So there are no needs to
# specialize `==`, `<`, and `<=` to handle these cases, only `cmp` may be specialized. For
# big floats, `cmp` converts the non-big operand to a big float so there nothing to do
# here. For big integers, `cmp` with a non-big integer `c` of size not larger than a
# `Clong` calls one of the compiled methods with `c` as a `Clong` or as a `Culong`. Hence,
# we only have to specialize `cmp` for a big integer and a neutral number.
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
# As can be seen in `base/mpfr.jl`, for the addition or subtraction of a big float with
# `c`, an integer of size ≤ `sizeof(Clong)`, the operation calls one of the compiled
# methods with `c` a `Clong` or a `Culong`. Benchmarking shows no real differences between
# the two so, in order to make the code similar as the one for big integers, we manage
# to convert `c` or `-c` to a `Culong`.
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

        # Less than.
        Base.:<(x::$T, y::Neutral) = x < Clong(y)
        Base.:<(x::Neutral, y::$T) = Clong(x) < y

        # Less or equal.
        Base.:<=(x::$T, y::Neutral) = x <= Clong(y)
        Base.:<=(x::Neutral, y::$T) = Clong(x) <= y
    end
end

#-----------------------------------------------------------------------------------------

function __init__()
    @static if !isdefined(Base, :get_extension)
        # Extend methods when other packages are loaded.
        @require Unitful = "1986cc42-f94f-5a68-af5c-568840ba703d" include(
            "../ext/NeutralsUnitfulExt.jl")
    end
end

end
