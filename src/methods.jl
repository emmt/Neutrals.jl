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

#---------------------------------------------------------------------------- Constructors -

# For numbers, there is no needs to extend `Base.convert` with the following "conversion"
# constructors as `Base.convert(T, x)` falls back to call `T(x)::T`.
Neutral(x::Neutral) = x
Neutral{V}(x::Neutral{V}) where {V} = x
Neutral{V}(x::Neutral) where {V} = throw(InexactError(:convert, Neutral{V}, x))
Neutral(x::Int) = Neutral{x}()
for type in (:Number, :Rational, :Complex, :BigFloat) # `Number` is not enough to get rid of ambiguities
    @eval begin
        Neutral(x::$type) = Neutral(Int(x)::Int)
        Neutral{V}(x::$type) where {V} =
            x == V ? Neutral{V}() : throw(InexactError(:convert, Neutral{V}, x))
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

#------------------------------------------------------------------------ Unary operations -

# For integers, `Base.rem(x, T)` may be used to "convert" `x` to type `T`.
Base.rem(x::Neutral, ::Type{Integer}) = x
Base.rem(::Neutral{x}, ::Type{T}) where {x,T<:Integer} = x % T
for T in (:Bool, :BigInt) # remove ambiguities for these types
    @eval Base.rem(::Neutral{x}, ::Type{$T}) where {x} = x % $T
end

Base.modf(x::Neutral) = (ZERO, x)

Base.widen(x::Neutral) = x
Base.widen(::Type{T}) where {T<:Neutral} = T

#------------------------------------------------------------------------- Promotion rules -

"""
    Neutrals.type_common(x) -> T
    Neutrals.type_common(typeof(x)) -> T

Return the dimensionless type `T` to convert a neutral number operand in common binary
operations (additions, subtractions, and comparisons) when the other operand is of the type
of `x`.

See also [`Neutrals.type_signed`](@ref), [`Neutrals.impl_add`](@ref),
[`Neutrals.impl_sub`](@ref), [`Neutrals.impl_eq`](@ref), [`Neutrals.impl_lt`](@ref),
[`Neutrals.impl_le`](@ref), and [`Neutrals.impl_cmp`](@ref).

"""
type_common(x::Number) = type_common(typeof(x))
type_common(::Type{T}) where {T<:Number} = _type_common(bare_type(T))
_type_common(::Type{T}) where {T<:Real} = T
_type_common(::Type{T}) where {T<:AbstractIrrational} = Float64
_type_common(::Type{Rational{T}}) where {T} = _type_common(T)
_type_common(::Type{Complex{T}}) where {T} = _type_common(T)
_type_common(::Type{BigInt}) = Clong # see `base/gmp.jl`
_type_common(::Type{BigFloat}) = Clong # see `base/mpfr.jl`

"""
    Neutrals.type_signed(x) -> T
    Neutrals.type_signed(typeof(x)) -> T

Return the dimensionless type `T` to convert a neutral number operand in some binary
operations (quotient or remainder of truncated division, and modulo) when the other operand
is of the type of `x` and when the signedness of the neutral number must be preserved to
reflect the usual behavior of the binary operation in Julia.

See also [`Neutrals.type_common`](@ref), [`Neutrals.impl_tdv`](@ref),
[`Neutrals.impl_rem`](@ref), and [`Neutrals.impl_mod`](@ref).

"""
type_signed(x::Number) = type_signed(typeof(x))
type_signed(::Type{T}) where {T<:Number} = _type_signed(bare_type(T))

# NOTE For `div`, `rem`, and `mod` with a big number, the other operand is promoted to a
#      big number. Thus, the rule for `Real` is also suitable for big numbers.
_type_signed(::Type{T}) where {T<:Real} = T
_type_signed(::Type{T}) where {T<:AbstractIrrational} = Float64
_type_signed(::Type{Rational{T}}) where {T} = _type_signed(T)
_type_signed(::Type{Complex{T}}) where {T} = _type_signed(T)
_type_signed(::Type{T}) where {T<:Signed} = T

# NOTE Not all versions of Julia implement `signed(T)`.
for (U, S) in (:UInt8 => :Int8, :UInt16 => :Int16, :UInt32 => :Int32,
               :UInt64 => :Int64, :UInt128 => :Int128)
    @eval _type_signed(::Type{$U}) = $S
end

# Extend `Base.promote_rule` when one of the argument is a neutral number. For two neutral
# numbers, the default is to convert them to `Int`. For `Bool`, the symmetric promote rule
# must be given to avoid overflows.
Base.promote_rule(::Type{<:Neutral}, ::Type{<:Neutral}) = Int
Base.promote_rule(::Type{<:Neutral}, ::Type{T}) where {T<:Number} = T
Base.promote_rule(::Type{<:Neutral}, ::Type{<:AbstractIrrational}) = Float64
Base.promote_rule(::Type{Bool}, ::Type{<:Neutral}) = Bool
Base.promote_rule(::Type{Bool}, ::Type{<:Neutral{-1}}) = Int
Base.promote_rule(::Type{<:Neutral{-1}}, ::Type{Bool}) = Int

#---------------------------------------------------------------------------------- Ranges -

# Considering the specific cases `step = 𝟘` and `start = step = stop = -𝟙` is to avoid
# stack overflows.
Base.:(:)(start::Integer, step::Neutral{0}, stop::Integer) = throw(ArgumentError("step cannot be zero"))
Base.:(:)(start::Integer, step::Neutral{1}, stop::Integer) = start:stop
Base.:(:)(start::Integer, step::Neutral{-1}, stop::Integer) = (:)(promote(start, step, stop)...)
Base.:(:)(start::Neutral{-1}, step::Neutral{-1}, stop::Neutral{-1}) = -ONE:-ONE

Base.:(:)(start::Neutral{1}, stop::Neutral{1}) = Base.OneTo(ONE)
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
