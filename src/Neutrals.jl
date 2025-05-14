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

@public @encode_rules
@public value
@public add sub mul rdiv pow eq lt leq
@public lshft rshft urshft bitwise_or bitwise_and bitwise_xor

"""
    Neutral{V}()
    Neutral(V)

yield a neutral number of value `V` (one of `0`, `1`, or `-1`) which implement the
following properties:

* `Neutral(0)` is the neutral element for the addition of numbers and is a *strong zero*
  for the multiplication of numbers.

* `Neutral(1)` is the neutral element for the multiplication of numbers.

* Multiplying by `Neutral(-1)` always negate the other operand.

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
# which calls `T(x)` for numbers. With unsigned numbers, an `InexactError` will be thrown
# for `-ONE`.
for T in (Bool,
          Int8, Int16, Int32, Int64, Int128, BigInt,
          UInt8, UInt16, UInt32, UInt64, UInt128,
          Float16, Float32, Float64, BigFloat)
    @eval (::Type{$T})(::Neutral{x}) where {x} = $T(x)
end
(::Type{Rational{T}})(::Neutral{x}) where {x,T<:Integer} = Rational{T}(x)
(::Type{Complex{T}})(::Neutral{x}) where {x,T<:Integer} = Complex{T}(x, 0)
(::Type{AbstractFloat})(::Neutral{x}) where {x} = Float64(x)

# Extend unary `-` for neutral numbers. Unary `+`, `*`, `&`, `|`, and `xor` do not need to
# be extended for numbers (see base/operators.jl).
Base.:(-)(x::Neutral{0}) = ZERO
Base.:(-)(x::Neutral{1}) = Neutral(-1) # NOTE do not use expression `-ONE` here
Base.:(-)(x::Neutral{-1}) = ONE

# Bitwise not.
Base.:(~)(x::Neutral{0}) = -ONE
Base.:(~)(x::Neutral{1}) = -2 # FIXME is this useful?
Base.:(~)(x::Neutral{-1}) = ZERO

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
Base.signbit(x::Union{Neutral{0},Neutral{1}}) = false
Base.signbit(x::Neutral{-1}) = true
#
for f in (:abs, :abs2)
    @eval begin
        Base.$f(x::Union{Neutral{0},Neutral{1}}) = x
        Base.$f(x::Neutral{-1}) = ONE
    end
end
#
Base.angle(::Union{Neutral{0},Neutral{1}}) = ZERO
Base.angle(::Neutral{-1}) = π
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

# Neutral numbers of different values have different types but promotion of neutral
# numbers does not change their types (see above promotion rules). Hence, rules for binary
# operations between neutral numbers must be explicitly implemented even though the
# default implementation of some operations would work when the two neutral operands have
# the same value.
for x in instances(Neutral), y in instances(Neutral)
    for f in (:(==), :isequal, :(<), :(<=), :isless, :(+), :(-), :(*), :(|), :(&), :(xor),
              :(<<), :(>>), :(>>>))
        r = @eval $f(Int($x), Int($y))
        if r isa Bool
            @eval Base.$f(::$(typeof(x)), ::$(typeof(y))) = $r
        elseif r ∈ (0, 1, -1) # returns a neutral number if possible
            @eval Base.$f(::$(typeof(x)), ::$(typeof(y))) = $(Neutral{r}())
        else # otherwise returns an integer
            @eval Base.$f(::$(typeof(x)), ::$(typeof(y))) = $r
        end
    end
    # Division, modulo, etc.
    for f in (:(/), :div, :rem, :mod)
        if y === ZERO
            @eval Base.$f(::$(typeof(x)), ::$(typeof(y))) = throw(DivideError())
        else # y is ONE or -ONE
            r = if f === :(/)
                Int(x)*Int(y) # x/y yields the same result as x*y when abs(y) = 1
            else
                @eval $f(Int($x), Int($y))
            end
            @eval Base.$f(::$(typeof(x)), ::$(typeof(y))) = $(Neutral{r}())
        end
    end
    # Exponentiation.
    if y === ZERO
        @eval Base.:(^)(::$(typeof(x)), ::$(typeof(y))) = ONE
    else
        @eval Base.:(^)(::$(typeof(x)), ::$(typeof(y))) = $x
    end
    # Comparison.
    @eval Base.cmp(::$(typeof(x)), ::$(typeof(y))) = $(cmp(Int(x), Int(y)))
end

# Extend `Base.promote_rule` when one of the argument is a neutral number. For `Bool`, the
# symmetric promote rule must be given to avoid overflows.
Base.promote_rule(::Type{<:Neutral}, ::Type{<:Neutral}) = Neutral
Base.promote_rule(::Type{<:Neutral}, ::Type{T}) where {T<:Number} = T
Base.promote_rule(::Type{Bool}, ::Type{<:Neutral}) = Bool

# For some binary operations involving neutral numbers, it is sufficient to apply the
# operation for the arguments promoted according to promotion rules. Other operations must
# be specialized because either the operation has a specific "hard-coded" result (e.g.
# ONE*x -> x or x + ZER0 -> x) or the promotion rules are inappropriate.
#
# For binary operations, the usual operators and functions may be overridden for sub-types
# of `Number`, e.g. to apply specific promotion rules. To simplify the code, we split the
# work of specializing binary operators/functions for a number and a neutral number in two
# stages: (1) extend the operator/function for different types of numbers and a neutral
# number to call (2) a non-exported function of this package. The 1st stage solves
# ambiguities while the 2nd makes easier to implement specific behaviors and to extend the
# package for other numeric types (such as `Unitful` quantities).
#
# Addition: ZERO is the neutral element.
add(x::Neutral, y::Number) = add(y, x) # addition is commutative
add(x::Number, ::Neutral{ 0}) = x
add(x::Number, ::Neutral{y}) where {y} = x + convert(typeof(x), y)
#
# Subtraction. Logic follows from that of the addition and multiplication.
sub(::Neutral{0}, y::Number) = -y
sub(::Neutral{x}, y::Number) where {x} = convert(typeof(y), x) - y
sub(x::Number, ::Neutral{ 0}) = x
sub(x::Number, ::Neutral{y}) where {y} = x - convert(typeof(x), y)
#
# Multiplication: ONE is the neutral element, ZERO is a strong zero.
mul(x::Number, y::Neutral) = mul(y, x) # multiplication is commutative
mul(::Neutral{ 0}, x::Number) = ZERO
mul(::Neutral{ 1}, x::Number) = x
mul(::Neutral{-1}, x::Number) = -x
#
# Right-division.
rdiv(::Neutral{ 0}, x::Number) = ZERO
rdiv(::Neutral{ 1}, x::Number) = inv(x)
rdiv(::Neutral{-1}, x::Number) = -inv(x)
rdiv(x::Number, ::Neutral{ 0}) = throw(DivideError())
rdiv(x::Number, ::Neutral{ 1}) = x
rdiv(x::Number, ::Neutral{-1}) = -x
#
# Exponentiation
pow(x::Number, ::Neutral{ 0}) = oneunit(x)
pow(x::Number, ::Neutral{ 1}) = x
pow(x::Number, ::Neutral{-1}) = inv(x)
#
# Equality (`==` or `isequal`).
eq(x::Neutral, y::Number) = eq(y, x) # equality is commutative
eq(x::Number, ::Neutral{ 0}) = is_dimensionless(x) && iszero(x)
eq(x::Number, ::Neutral{ 1}) = isone(x)
eq(x::Number, ::Neutral{-1}) = is_signed(x) && x == -one(x)
#
# Less than `<` or `isless`).
lt(x::Number, ::Neutral{ 0}) = is_signed(x) && x < zero(x)
lt(x::Number, ::Neutral{ 1}) = x < one(x)
lt(x::Number, ::Neutral{-1}) = is_signed(x) && x < -one(x)
lt(::Neutral{ 0}, x::Number) = zero(x) < x
lt(::Neutral{ 1}, x::Number) = one(x) < x
lt(::Neutral{-1}, x::Number) = !is_signed(x) || -one(x) < x
#
# Less or equal `<` or `isless`).
leq(x::Number, ::Neutral{ 0}) = x ≤ zero(x) # FIXME dimensionless
leq(x::Number, ::Neutral{ 1}) = x ≤ one(x)
leq(x::Number, ::Neutral{-1}) = is_signed(x) && x ≤ -one(x)
leq(::Neutral{ 0}, x::Number) = zero(x) ≤ x
leq(::Neutral{ 1}, x::Number) = one(x) ≤ x
leq(::Neutral{-1}, x::Number) = !is_signed(x) || -one(x) ≤ x
#
# Bitwise or `|`.
bitwise_or(x::Integer, ::Neutral{0}) = x
bitwise_or(x::Integer, ::Neutral{1}) = x | one(x)
bitwise_or(x::Integer, ::Neutral{-1}) = -one(x) # FIXME Bool, Unsigned
#
# Bitwise and `&`.
bitwise_and(x::Integer, ::Neutral{0}) = zero(x)
bitwise_and(x::Integer, ::Neutral{1}) = x & one(x)
bitwise_and(x::Integer, ::Neutral{-1}) = x # FIXME not for Bool, Unsigned?
#
# Bitwise xor `⊻`.
bitwise_xor(x::Integer, ::Neutral{0}) = x
bitwise_xor(x::Integer, ::Neutral{1}) = xor(x, one(x))
bitwise_xor(x::Integer, ::Neutral{-1}) = xor(x, -one(x))
#
# Bitwise left-shift `<<` (see base/int.jl).
lshft(x::Integer, ::Neutral{0}) = x
lshft(x::Integer, ::Neutral{1}) = x << UInt(1)
lshft(x::Integer, ::Neutral{-1}) = x >> UInt(1)
#
# Bitwise right-shift `>>` (see base/int.jl).
rshft(x::Integer, ::Neutral{0}) = x
rshft(x::Integer, ::Neutral{1}) = x >> UInt(1)
rshft(x::Integer, ::Neutral{-1}) = x << UInt(1)
#
# Bitwise unsigned right-shift `>>>` (see base/int.jl).
urshft(x::Integer, ::Neutral{0}) = x
urshft(x::Integer, ::Neutral{1}) = x >>> UInt(1)
urshft(x::Integer, ::Neutral{-1}) = x << UInt(1)
#

is_dimensionless(x::Number) = is_dimensionless(typeof(x))
is_dimensionless(::Type{<:Number}) = true

macro encode_rules(type, is_int::Bool)
    # NOTE `type` is defined in the caller's context
    code = encode_rules(esc(type), is_int)
    quote
        $(code...)
    end
end

function encode_rules(type, is_int::Bool)
    code = Expr[]
    # Binary operations for which any operand may be a neutral number.
    for (f, g) in (:(+)     => :add,
                   :(-)     => :sub,
                   :(*)     => :mul,
                   :(/)     => :rdiv,
                   :div     => :rdiv,
                   :(==)    => :eq,
                   :isequal => :eq,
                   (:<)     => :lt,
                   :isless  => :lt,
                   :(≤)     => :leq)
        push!(code, :(Base.$f(x::Neutral, y::$type) = $g(x, y)))
        push!(code, :(Base.$f(x::$type, y::Neutral) = $g(x, y)))
    end
    # Binary operations for which only the right operand may be a neutral number.
    push!(code, :(Base.:(^)(x::$type, y::Neutral) = pow(x, y)))
    if is_int
        for (f, g) in (:(|)   => :bitwise_or,
                       :(&)   => :bitwise_and,
                       :xor   => :bitwise_xor,
                       :(<<)  => :lshft,
                       :(>>)  => :rshft,
                       :(>>>) => :urshft)
            push!(code, :(Base.$f(x::$type, y::Neutral) = $g(x, y)))
        end
    end
    #foreach(x -> println(stderr, x), code)
    return code
end

@encode_rules Number false
@encode_rules Integer true
@encode_rules BigInt true
@encode_rules BigFloat false

# In Julia, Booleans are promoted to `Int` for a number of binary operations (see
# base/bool.jl): addition, subtraction with non-zero neutrals, and bitwise shifts.
#
add(x::Bool, y::NonZeroNeutral) = Int(x) + Int(y)
#
sub(x::Bool, y::NonZeroNeutral) = Int(x) - Int(y)
sub(x::NonZeroNeutral, y::Bool) = Int(x) - Int(y)
#
lshft(x::Bool, y::Neutral) = lshft(Int(x), y)
rshft(x::Bool, y::Neutral) = rshft(Int(x), y)
urshft(x::Bool, y::Neutral) = ushft(Int(x), y)

# Avoid promotion for comparison with Booleans.
eq(x::Bool, y::Neutral{1}) = x
eq(x::Bool, y::Neutral{0}) = !x
eq(x::Bool, y::Neutral{-1}) = false
#
Base.cmp(x::Neutral, y::Bool) = -cmp(y, x)
Base.cmp(x::Bool, y::Neutral{-1}) = 1
Base.cmp(x::Bool, y::Neutral{ 0}) = ifelse(x, 1, 0)
Base.cmp(x::Bool, y::Neutral{ 1}) = ifelse(x, 0, -1)

# For some binary operation involving a big integer or float and a neutral number, avoid
# costly promotion of the neutral number to a `BigInt` or a `BigFloat` by converting it to
# a `Clong` (see `base/gmp.jl` and `base/mpfr.jl`).
Base.cmp(x::BigNumber, y::Neutral) = cmp(x, Clong(y))
Base.cmp(x::Neutral, y::BigNumber) = cmp(Clong(x), y)
#
add(x::BigNumber, y::NonZeroNeutral) = x + Clong(y)
#
sub(x::BigNumber, y::NonZeroNeutral) = x - Clong(y)
sub(x::NonZeroNeutral, y::BigNumber) = Clong(x) - y

end
