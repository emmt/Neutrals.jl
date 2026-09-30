"""
    Neutrals.static_value(x::Neutral)
    Neutrals.static_value(typeof(x)::Type{<:Neutral})

Return the static value of the neutral number `x`. The result is an integer (of type `Int`)
whose value only depends on the of `x`.

"""
static_value(x::Neutral) = static_value(typeof(x))
static_value(::Type{Neutral{X}}) where {X} = X

# NOTE This method is not type stable and should only be used in a context where its result
#      can be inferred.
@inline maybe_neutral(z::Int) = -1 <= z <= 1 ? Neutral{z}() : z

function Base.show(io::IO, x::Neutral)
    v = static_value(x)
    if v == -1
        print(io, VERSION ≥ v"1.3" ? "-𝟙" : "-ONE")
    elseif v == 0
        print(io, VERSION ≥ v"1.3" ? "𝟘" : "ZERO")
    elseif v == 1
        print(io, VERSION ≥ v"1.3" ? "𝟙" : "ONE")
    else
        print(io, "Neutral{", v, "}()")
    end
end

Base.summary(io::IO, x::Neutral) = print(io, summary(x))
function Base.summary(x::Neutral)
    v = static_value(x)
    return (v == -1 ? "opposite of neutral element for the multiplication of numbers" :
            v ==  0 ? "neutral element for the addition of numbers" :
            v ==  1 ? "neutral element for the multiplication of numbers" : "Neutral{$v}()")
end

for (f, n) in (:zero => ZERO, :one => ONE, :oneunit => ONE)
    @eval begin
        Base.$f(x::Neutral) = $f(typeof(x))
        Base.$f(::Type{<:Neutral}) = $n
    end
end

for (f, ex) in (:iszero     => :(static_value(x) == 0),
                :isone      => :(static_value(x) == 1),
                :ispositive => :(static_value(x) > 0),
                :isnegative => :(static_value(x) < 0),
                :sign       => :(static_value(x) < 0 ? -1 : static_value(x) > 0 ? 1 : 0))
    g = isdefined(Base, f) ? :(Base.$f) : f
    @eval $g(x::Neutral) = $ex
end

Base.signbit(x::Neutral) = isnegative(x)

for f in (:abs, :abs2)
    @eval Base.$f(x::Neutral) = Neutral{$f(static_value(x))}()
end
Base.checked_abs(x::Neutral) = abs(x)

Base.isodd(x::Neutral) = (static_value(x) & 1) == 1
Base.iseven(x::Neutral) = (static_value(x) & 1) == 0

Base.angle(x::Neutral) = isnegative(x) ? π : ZERO

Base.inv(x::Neutral) = ONE/x

# Extend unary `-` for neutral numbers. Unary `+`, `*`, `&`, `|`, and `xor` do not need to
# be extended for numbers (see base/operators.jl).
Base.:(-)(x::Neutral) = Neutral{-static_value(x)}()

# Bitwise not. Yield an `Int` if result cannot be represented by a neutral number.
Base.:(~)(x::Neutral) = maybe_neutral(~static_value(x))

#----------------------------------------------------------------------------- Conversions -
#
# Numeric type constructors are called by `convert` in its default implementation. We
# therefore extend numeric type constructors, not `convert`.
#
# Abstract numeric type constructors (Number, Real, Integer, and Neutral need no
# specialization).
(::Type{Signed})(x::Neutral) = Int(x)
(::Type{Unsigned})(x::Neutral) = UInt(x)
(::Type{Rational})(x::Neutral) = Rational{Int}(static_value(x), 1)
(::Type{AbstractFloat})(x::Neutral) = float(static_value(x)) # also used by `float(x)`
(::Type{T})(x::Neutral) where {T<:AbstractIrrational} = throw(InexactError(:convert, T, x))
function (::Type{Complex})(x::Neutral) # also used by `complex(x)`
    iszero(x) && return Complex(false, false)
    isone(x) && return Complex(true, false)
    return Complex(static_value(x), 0)
end

# Concrete numeric constructors. `Complex{T}` and `Rational{T}` need not be extended.
#Base.Rational{T}(x::Neutral) where {T<:Integer} = Rational(T(x))
#Base.Complex{T}(x::Neutral) where {T<:Real} = Complex(T(x), zero(T))
(::Type{Int})(x::Neutral) = static_value(x)
function (::Type{Bool})(x::Neutral)
    iszero(x) && return false
    isone(x) && return true
    throw(InexactError(:Bool, Bool, x))
end

# Conversion rules for bare numeric types. No needs to extend `Base.convert` because
# `Base.convert(T,x)` amounts to calling `T(x)` for any numeric type `T`. Direct conversion
# by `T(x)` for `T` one of the basic numeric types is also needed by some functions. For
# example, `Float32(x)` and `Float64(x)` are used by `copysign` and `flipsign`.
for T in BITS_REAL
    if T <: Unsigned
        @eval function (::Type{$T})(x::Neutral)
            isnegative(x) && throw(InexactError($(QuoteNode(Symbol(T))), $T, x))
            return $T(static_value(x))
        end
    elseif !(T <: Union{Bool,Int})
        @eval (::Type{$T})(x::Neutral) = $T(static_value(x))
    end
end
for T in (BigInt, BigFloat)
    @eval function (::Type{$T})(x::Neutral)
        iszero(x) && return zero($T)
        isone(x) && return one($T)
        return $T(aritmetic_operand($T, x))
    end
end

# For integers, `Base.rem(x, T)` may be used to "convert" `x` to type `T`.
Base.rem(x::Neutral, ::Type{Integer}) = x
Base.rem(x::Neutral, ::Type{Neutral}) = x
Base.rem(x::Neutral, ::Type{T}) where {T<:Integer} = static_value(x) % T
for T in (:Bool, :BigInt) # remove ambiguities for these types
    @eval Base.rem(x::Neutral, ::Type{$T}) = static_value(x) % $T
end

Base.modf(x::Neutral) = (ZERO, x)

Base.widen(x::Neutral) = x
Base.widen(::Type{T}) where {T<:Neutral} = T

# Outer constructors.
(::Type{Neutral})(x::Neutral) = x
(::Type{Neutral})(x::Int) = Neutral{x}()
for T in (:Number, :Rational, :Complex, :BigFloat)
    @eval begin
        (::Type{Neutral})(x::$T) = Neutral(convert(Int, x))
        function (::Type{Neutral{V}})(x::$T) where {V}
            isequal(x, V) || throw(InexactError(:convert, Neutral{V}, x))
            return Neutral{V}()
        end
    end
end

# Error catcher.
Neutral{V}() where {V} = throw(ArgumentError(
    "value "*(V isa Number ? repr(V) : "of type `$(typeof(V))`")
    *" cannot be converted into a neutral number"))

#---------------------------------------------------------------------------- Base methods -

Base.typemin(::Type{Neutral}) = -ONE
Base.typemin(::Type{<:Neutral{x}}) where {x} = Neutral{x}()
Base.typemax(::Type{Neutral}) = ONE
Base.typemax(::Type{<:Neutral{x}}) where {x} = Neutral{x}()

#------------------------------------------------------- Extend methods from other packages -

# Extend methods defined in `TypeUtils`.
TypeUtils.is_signed(::Type{<:Neutral}) = true
TypeUtils.is_static_number(::Type{<:Neutral}) = true
TypeUtils.get_precision(::Type{<:Neutral}) = AbstractFloat
TypeUtils.adapt_precision(::Type{<:TypeUtils.Precision}, x::Neutral) = x
TypeUtils.adapt_precision(::Type{<:TypeUtils.Precision}, ::Type{T}) where {T<:Neutral} = T

#------------------------------------------------------------------------- Promotion rules -

# Extend `Base.promote_rule` when one of the argument is a neutral number. For two neutral
# numbers, the default is to convert them to `Int`. For `Bool`, the symmetric promote rule
# must be given to avoid stack overflows.
Base.promote_rule(::Type{<:Neutral}, ::Type{<:Neutral}) = Int
Base.promote_rule(::Type{<:Neutral}, ::Type{T}) where {T<:Union{Real,Complex}} = T
Base.promote_rule(::Type{<:Neutral}, ::Type{<:AbstractIrrational}) = Float64
Base.promote_rule(::Type{Bool}, ::Type{<:Neutral}) = Int
Base.promote_rule(::Type{<:Neutral}, ::Type{Bool}) = Int

"""
    Neutrals.infinity(x)

Return a suitable value to represent infinity of the same sign as `x` and of type
suitable for `x`.

"""
infinity(x::Real) = copysign(Inf, x)
infinity(x::Rational{T}) where {T} = copysign(one(T), x)//zero(T)
infinity(x::T) where {T<:AbstractFloat} = copysign(convert(T, Inf)::T, x)
infinity(x::T) where {T<:Complex} = complex(infinity(real(x)), infinity(imag(x)))
# FIXME generalize to numbers and deal with units?

#---------------------------------------------------------------------------------- Ranges -

# Considering the specific cases `step = 𝟘` and `start = step = stop = -𝟙` is to avoid
# stack overflows.
function Base.:(:)(start::Integer, step::Neutral, stop::Integer)
    step isa Neutral{0} && throw(ArgumentError("step cannot be zero"))
    step isa Neutral{1} && return start:stop
    return (:)(promote(start, step, stop)...)
end

# FIXME Base.:(:)(start::Neutral{-1}, step::Neutral{-1}, stop::Neutral{-1}) = -ONE:-ONE

Base.:(:)(start::Neutral{1}, stop::Neutral) = Base.OneTo(Int(stop))
Base.:(:)(start::Neutral{1}, stop::Integer) = Base.OneTo(stop)

Base.length(r::UnitRange{T}) where {T<:Neutral} = 1
Base.first(r::UnitRange{T}) where {T<:Neutral} = T()
Base.last(r::UnitRange{T}) where {T<:Neutral} = T()

# This fix is needed for Julia versions < 1.8.0-beta1 in order to be able to build a
# UnitRange with start and stop being the same neutral number. Such as `𝟙:𝟙`.
if VERSION < v"1.8.0-beta1" && isdefined(Base, :unitrange_last)
    Base.unitrange_last(start::T, stop::T) where {T<:Neutral} = stop
end

#------------------------------------------------------------------- Arithmetic operations -

"""
    Neutrals.aritmetic_operand(T, x::Neutral) -> xp

Return a value `xp` equivalent to that of `x` and with efficient type for an arithmetic
operation like the addition involving an operand of type `T` and operand `x`.

# See also

[`Neutrals.comparative_operand`](@ref) for comparison operations and
[`Neutrals.bitwise_operand`](@ref) for bitwise operations.

"""
function aritmetic_operand(::Type{T}, x::Neutral) where {T<:Real}
    return convert(T, x)
end
function aritmetic_operand(::Type{T}, x::Neutral) where {T<:Bool}
    return static_value(x)::Int
end
function aritmetic_operand(::Type{T}, x::Neutral) where {T<:Unsigned}
    return isnegative(x) ? -signed(convert(T, -x)) : convert(T, x) # FIXME signed not needed?
end
function aritmetic_operand(::Type{<:Union{Rational{T},Complex{T}}}, x::Neutral) where {T}
    return convert(T, x)
end
function aritmetic_operand(::Type{<:AbstractIrrational}, x::Neutral)
    return float(x)
end
function aritmetic_operand(::Type{T}, x::Neutral) where {T<:BigReal}
    return isnegative(x) ? Clong(x) : Culong(x)
end
# Addition.

Base.:(+)(x::Neutral, y::Neutral) = maybe_neutral(static_value(x) + static_value(y))

for T in (Integer, Rational, Real)
    @eval begin
        Base.:(+)(x::Neutral, y::$T) = y + x # addition is symmetric

        function Base.:(+)(x::$T, y::Neutral)
            isnegative(y) && return x - aritmetic_operand(typeof(x), -y)
            ispositive(y) && return x + aritmetic_operand(typeof(x),  y)
            return x
        end
    end
end

# Subtraction.

Base.:(-)(x::Neutral, y::Neutral) = maybe_neutral(static_value(x) - static_value(y))

for T in (Integer, Real, Rational)
    @eval begin
        function Base.:(-)(x::$T, y::Neutral)
            ispositive(y) && return x - aritmetic_operand(typeof(x),  y)
            isnegative(y) && return x + aritmetic_operand(typeof(x), -y)
            return x
        end

        function Base.:(-)(x::Neutral, y::$T)
            iszero(x) && return -y
            return aritmetic_operand(typeof(y), x) - y
        end
    end
end

# Multiplication.

Base.:(*)(x::Neutral, y::Neutral) = Neutral{static_value(x)*static_value(y)}()

for T in (Integer, Rational, AbstractIrrational, Real, Complex, Complex{Bool})
    @eval begin
        Base.:(*)(x::$T, y::Neutral) = y * x # multiplication is symmetric
        function Base.:(*)(x::Neutral, y::$T)
            iszero(x) && return ZERO # propagate strong zero
            isone(x) && return y
            return -y
        end
    end
end

# Division.

function Base.:(/)(x::Neutral, y::Neutral)
    if iszero(y)
        iszero(x) && return NaN
        isone(x) && return Inf
        return -Inf
    end
    isone(y) && return x
    return -x
end

for T in (Integer, Rational, AbstractIrrational, Real, Complex)
    @eval begin
        function Base.:(/)(x::$T, y::Neutral)
            if iszero(y)
                x isa Complex && return complex(infinity(real(x)), infinity(imag(x)))
                return infinity(x)
            end
            isone(y) && return x
            return -x
        end
        function Base.:(/)(x::Neutral, y::$T)
            iszero(x) && return ZERO # propagate strong zero
            isone(x) && return inv(y)
            return -inv(y)
        end
    end
end

#---------------------------------------------------------------------- Bitwise operations -

"""
    Neutrals.bitwise_operand(T, x::Neutral) -> xp

Return a value `xp` equivalent to that of `x` and with efficient type for a bitwise
operation involving an operand of type `T` and operand `x`.

# See also

[`Neutrals.comparative_operand`](@ref) for comparison operations and
[`Neutrals.aritmetic_operand`](@ref) for arithmetic operations.

"""
function bitwise_operand(::Type{T}, x::Neutral) where {T<:Union{Bool,Unsigned}}
    x isa Neutral{-1} && return ~zero(T)
    return convert(T, static_value(x))
end
function bitwise_operand(::Type{T}, x::Neutral) where {T<:Integer} # also BigInt
    return aritmetic_operand(T, x)
end

# Bitwise operations when the two operands are neutral numbers.
Base.:(|)(x::Neutral, y::Neutral) = Neutral{static_value(x) | static_value(y)}()
Base.:(&)(x::Neutral, y::Neutral) = Neutral{static_value(x) & static_value(y)}()
Base.:(⊻)(x::Neutral, y::Neutral) =
    maybe_neutral(static_value(x) ⊻ static_value(y))

# Bitwise operations are symmetric.
Base.:(|)(x::Neutral, y::Integer) = (y | x)
Base.:(&)(x::Neutral, y::Integer) = (y & x)
Base.:(⊻)(x::Neutral, y::Integer) = (y ⊻ x)

function Base.:(|)(x::Integer, y::Neutral)
    iszero(y) && return x
    y isa Neutral{-1} && return ~zero(x) # FIXME propagate -ONE?
    return x | bitwise_operand(typeof(x), y)
end

function Base.:(&)(x::Integer, y::Neutral)
    iszero(y) && return zero(x) # FIXME propagate ZERO?
    y isa Neutral{-1} && return x
    return x & bitwise_operand(typeof(x), y)
end

function Base.:(⊻)(x::Integer, y::Neutral)
    iszero(y) && return x
    y isa Neutral{-1} && return ~x
    return x ⊻ bitwise_operand(typeof(x), y)
end

#------------------------------------------------------------------------------ Bit shifts -

# In Julia, the type of `x << y`, `x >> y`, and `x >>> y` is determined by `x`, not by `y`:
# the result is an `Int` if `x` is a Boolean and the result has the same type as `x`
# otherwise.
#
# In Julia implementation, the direction of shift is reversed if `y` is negative, so that
# the number of bits to shift can be specified as an `UInt`. We do the same here when `y` is
# a neutral number.

for (op, f) in (:(<<) => :lshft, :(>>) => :rshft, :(>>>) => :urshft)
    @eval Base.$op(x::Neutral, y::Neutral) = maybe_neutral($f(static_value(x), y))
    for T in (Bool, Integer)
        @eval Base.$op(x::$T, y::Neutral) = $f(x, y)
    end
end

to_int(x::Bool) = x ? 1 : 0

# Left shift (<<).
function lshft(x::Bool, y::Neutral)
    ispositive(y) && return to_int(x) << (static_value(y) % UInt)
    isnegative(y) && return 0
    return to_int(x)
end
function lshft(x::Integer, y::Neutral)
    ispositive(y) && return x << (static_value(y) % UInt)
    isnegative(y) && return x >> ((-static_value(y)) % UInt)
    return x
end

# Right shift (>>).
function rshft(x::Bool, y::Neutral)
    ispositive(y) && return 0
    isnegative(y) && return to_int(x) << ((-static_value(y)) % UInt)
    return to_int(x)
end
function rshft(x::Integer, y::Neutral)
    ispositive(y) && return x >> (static_value(y) % UInt)
    isnegative(y) && return x << ((-static_value(y)) % UInt)
    return x
end

# Unsigned right shift (>>).
function urshft(x::Bool, y::Neutral)
    ispositive(y) && return 0
    isnegative(y) && return to_int(x) << ((-static_value(y)) % UInt)
    return to_int(x)
end
function urshft(x::Integer, y::Neutral)
    ispositive(y) && return x >>> (static_value(y) % UInt)
    isnegative(y) && return x << ((-static_value(y)) % UInt)
    return x
end

for T in (Integer, Unsigned, Int)
    @eval begin
        function Base.:(<<)(x::Neutral, y::$T)
            iszero(x) && return 0 # FIXME propagate ZERO?
            y isa Bool && return ifelse(y, static_value(x) << 1, static_value(x))
            return static_value(x) << y
        end
        function Base.:(>>)(x::Neutral, y::$T)
            iszero(x) && return 0 # FIXME propagate ZERO?
            y isa Bool && return ifelse(y, static_value(x) >> 1, static_value(x))
            return static_value(x) >> y
        end
        function Base.:(>>>)(x::Neutral, y::$T)
            iszero(x) && return 0 # FIXME propagate ZERO?
            y isa Bool && return ifelse(y, static_value(x) >>> 1, static_value(x))
            return static_value(x) >>> y
        end
    end
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
function comparative_operand(::Type{T}, x::Neutral) where {T<:Real}
    # Expression below throws with `InexactError` if `T` is `Unsigned` or `Bool` which is
    # exactly what we want as this case shall be handled before calling this function.
    return convert(T, static_value(x))
end

function comparative_operand(::Type{T}, x::Neutral) where {T<:Unsigned}
    v = static_value(x)
    return v < 0 ? -signed(convert(T, -v)) : convert(T, v)
end

function comparative_operand(::Type{T}, x::Neutral) where {S,T<:Rational{S}}
    # Base Julia has specialized code to compare rationals and integers.
    return comparative_operand(S, x)
end

function comparative_operand(::Type{T}, x::Neutral) where {T<:AbstractIrrational}
    return static_value(x)
end

function comparative_operand(::Type{T}, x::Neutral) where {T<:BigReal}
    return aritmetic_operand(T, x)
end

#@noinline comparative_operand(::Type{T}, x::Neutral{-1}) where {T<:NonnegativeNumber} =
#    throw(InexactError(:convert, T, -1))

# Equality and relations of order between two neutral numbers.
Base.:(==)(x::Neutral, y::Neutral) = typeof(x) == typeof(y)
for f in (:(<), :(<=), :cmp)
    @eval Base.$f(x::Neutral, y::Neutral) = $f(static_value(x), static_value(y))
end

for T in (Real, Rational, BigInt, BigFloat)
    @eval begin
        # Equality between a neutral number and a real.
        Base.:(==)(x::Neutral, y::$T) = (y == x) # `==` is commutative
        function Base.:(==)(x::$T, y::Neutral)
            # We assume that `iszero(x)` and `isone(x)` are not slower than `x == zero(x)` and
            # `x == one(x)`.
            y isa Neutral{0} && return iszero(x) # NOTE x must be dimensionless
            y isa Neutral{1} && return isone(x)
            isnegative(y) && x isa NonnegativeReal && return false
            return x == comparative_operand(typeof(x), y)
        end
    end
end

# Neutral numbers are integers and are thus never equal to irrational numbers.
Base.:(==)(x::AbstractIrrational, y::Neutral) = false
Base.:(==)(x::Neutral, y::AbstractIrrational) = false

for T in (Real, Rational, BigInt, BigFloat)
    @eval begin
        # Less than.
        function Base.:(<)(x::Neutral, y::$T)
            if y isa NonnegativeReal
                isnegative(x) && return true
                y isa Bool && return ispositive(x) ? false : y
            end
            return comparative_operand(typeof(y), x) < y
        end
        function Base.:(<)(x::$T, y::Neutral)
            if x isa NonnegativeReal
                !ispositive(y) && return false
                x isa Bool && return !x
            end
            return x < comparative_operand(typeof(x), y)
        end
        # Less or equal.
        function Base.:(<=)(x::Neutral, y::$T)
            if y isa NonnegativeReal
                !ispositive(x) && return true
                x isa Neutral{1} && y isa Bool && return y
            end
            return comparative_operand(typeof(y), x) <= y
        end
        function Base.:(<=)(x::$T, y::Neutral)
            if x isa NonnegativeReal
                isnegative(y) && return false
                x isa Bool && y isa Neutral{0} && return !x
                x isa Bool && y isa Neutral{1} && return true
            end
            return x <= comparative_operand(typeof(x), y)
        end
    end
end

# Except for floats, < and isless are the same.
# For floats, in `base/float.jl`:
#
#     isless(x, y) =  isnan(x) || isnan(b) ? !isnan(x) : x < y
#
Base.isless(x::AbstractFloat, y::Neutral) = isnan(x) ? false : x < y
Base.isless(x::Neutral, y::AbstractFloat) = isnan(y) ? true : x < y

for T in (Real, Integer, BigInt, BigFloat)
    @eval begin
        # Generic comparison between a neutral number and a real.
        Base.cmp(x::Neutral, y::$T) = -Base.cmp(y, x) # `cmp` is anti-commutative
        function Base.cmp(x::$T, y::Neutral)
            if x isa NonnegativeReal
                isnegative(y) && return 1
                y isa Neutral{0} && return iszero(x) ? 0 : 1
                x isa Bool && y isa Neutral{1} && return x ? 0 : -1
            end
            return ifelse(isless(x, y), -1, ifelse(isless(y, x), 1, 0))
        end
    end
end
