# Union of type of operands supporting the optimization of broadcasting rules.
const Operand{T<:Number} = Union{T,AbstractArray{<:T}}

"""
    Neutral{V}()
    Neutral(V)

yield a neutral number of value `V` (one of `0`, `1`, or `-1`) with the following
properties:

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
    ZERO
    𝟘    # for Julia ≤ 1.3

is a singleton representing a strong neutral element for the addition of dimensionless
numbers whose effect is to leave the other operand unchanged in an addition. More
specifically, whatever the type of the dimensionless number `x`, the following rules are
implemented:

    ZERO + x -> x + ZERO -> x
    x - ZERO -> x
    ZERO - x -> -x # i.e., negate x

When the above result is `x`, it means that the very same object is returned, e.g. `ZERO +
x === x` holds even though `x` is not an instance of an `isbitstype` type like `BigInt` or
`BigFloat`.

For consistency, with [`ONE`](@ref) or `𝟙`, the neutral element for the multiplication of
numbers, the following rules apply for the multiplication and the division involving
`ZERO`:

    x*ZERO -> ZERO*x -> ZERO
    ZERO/x -> ZERO

The type of `ZERO`, given by `typeof(ZERO)` or [`Neutral{0}`](@ref Neutral), is unique and
is a sub-type of `Real`.

"""
const ZERO = Neutral{0}()

"""
    ONE
    𝟙    # for Julia ≤ 1.3

yield a singleton representing the neutral element for the multiplication of numbers whose
effect is to leave the other operand unchanged in a multiplication. More specifically,
whatever the type of the number `x`, the following rules are implemented:

    x*ONE -> ONE*x -> x
    ONE\\x -> x/ONE -> x
    x\\ONE -> ONE/x -> inv(x)

When the above result is `x`, it means that the very same object is returned, e.g. `ONE*x
=== x` holds even though `x` is not an instance of an `isbitstype` type like `BigInt` or
`BigFloat`.

`-ONE`, the opposite of `ONE`, is also a singleton which may be used to represent a value
whose inferable effect is to negate the other operand. Multiplications and divisions with
`-ONE` follow the rules:

    x*(-ONE) -> (-ONE)*x -> -x
    (-ONE)\\x -> x/(-ONE) -> -x
    x\\(-ONE) -> (-ONE)/x -> -inv(x)

Compared to numerical values equal to `±1`, `ONE` and `-ONE` are singletons whose types
are unique and whose effects are known at compile time which opens possibilities to
optimize the code.

For consistency, with [`ZERO`](@ref) or `𝟘`, the neutral element for the addition of
dimensionless numbers, the following rules apply for the addition and subtraction:

    ONE - ONE -> ZERO
    ONE + (-ONE) -> ZERO
    etc.

The types of `ONE` and `-ONE`, given by `typeof(ONE)` and `typeof(-ONE)` or by
[`Neutral{1}`](@ref Neutral) and [`Neutral{-1}`](@ref Neutral), are both unique and are
sub-types of `Integer`.

"""
const ONE = Neutral{1}()

# Using `𝟘` and `𝟙` as names of constants is only supported for Julia ≥ 1.3.
if VERSION ≥ v"1.3"
    eval(Meta.parse("export 𝟘; const 𝟘 = ZERO; @doc (@doc ZERO) 𝟘;"))
    eval(Meta.parse("export 𝟙; const 𝟙 = ONE; @doc (@doc ONE) 𝟙;"))
end

@eval Base.instances(::Type{Neutral}) = $(map(v -> Neutral{v}(), (0, 1, -1)))

# Aliases to encode rules. `AnyNeutral` is more specific than `Neutral` and is a union of
# concrete types.
const AnyNeutral = Union{map(typeof, instances(Neutral))...}
const NonZeroNeutral = Union{Neutral{1},Neutral{-1}}
const NonNegativeNeutral = Union{Neutral{0},Neutral{1}}

# There are special rules for "unsigned" numbers which cannot be used to represent
# negative numbers.
const UnsignedRational = Rational{<:Union{Bool,Unsigned}}
const UnsignedReal = Union{Bool,Unsigned,UnsignedRational}
const UnsignedComplex = Complex{<:UnsignedReal}
const UnsignedNumber = Union{UnsignedReal,UnsignedComplex}

# `BareNumbers` are dimensionless.
const BareNumber = Union{Real,Complex}
