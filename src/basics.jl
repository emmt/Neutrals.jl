# Constructors, conversion, and basic methods for neutral numbers.

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

"""
    Neutrals.value(x)
    Neutrals.value(typeof(x))

Return the value associated with the neutral number `x`.

"""
value(::Neutral{x}) where x = x
value(::Type{<:Neutral{x}}) where x = x

"""
    Neutrals.is_dimensionless(x)
    Neutrals.is_dimensionless(typeof(x))

Return whether number `x` is dimensionless. This is a trait which only depends on the type
of `x`.

By default, only sub-types of `Real` and `Complex` are considered as being dimensionless.
This method must be extended for other numbers.

"""
is_dimensionless(x::Number) = is_dimensionless(typeof(x))
is_dimensionless(::Type{<:BareNumber}) = true

# Conversion rules for bare numeric types. No needs to extend `Base.convert` because
# `Base.convert(T,x)` amounts to calling `T(x)` for any numeric type `T`.
for T in (Bool,
          Int8, Int16, Int32, Int64, Int128, BigInt,
          UInt8, UInt16, UInt32, UInt64, UInt128,
          Float16, Float32, Float64, BigFloat)
    @eval (::Type{$T})(x::Neutral) = $T(value(x))
    if !is_signed(T)
        @eval (::Type{$T})(x::Neutral{-1}) = throw(InexactError(:convert, $T, x))
    end
end
(::Type{Number})(x::Neutral) = x
(::Type{Real})(x::Neutral) = x
(::Type{Integer})(x::Neutral) = x
(::Type{Rational{T}})(x::Neutral) where {T<:Integer} = Rational(T(x))
(::Type{Rational})(x::Neutral) = Rational(value(x), 1)
(::Type{Complex{T}})(x::Neutral) where {T<:Real} = Complex(T(x), T(0))
(::Type{Complex})(x::Neutral) = Complex(value(x), 0)
(::Type{AbstractFloat})(x::Neutral) = float(value(x))
(::Type{T})(x::Neutral) where {T<:AbstractIrrational} = throw(InexactError(:convert, T, x))

# Extend precision methods defined in `TypeUtils`.
TypeUtils.get_precision(::Type{<:Neutral}) = AbstractFloat
TypeUtils.adapt_precision(::Type{<:TypeUtils.Precision}, x::Neutral) = x
TypeUtils.adapt_precision(::Type{<:TypeUtils.Precision}, ::Type{X}) where {X<:Neutral} = X

#------------------------------------------------------------------------ Unary operations -

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

Base.modf(x::Neutral) = (ZERO, x)

Base.widen(x::Neutral) = x
Base.widen(::Type{T}) where {T<:Neutral} = T

#------------------------------------------------------------------------- Promotion rules -

"""
    Neutrals.type_common(x) -> T
    Neutrals.type_common(typeof(x)) -> T

yield the dimensionless type `T` to convert a neutral number operand in common binary
operations (additions, subtractions, and comparisons) when the other operand is of the
type of `x`.

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

yield the dimensionless type `T` to convert a neutral number operand in some binary
operations (quotient or remainder of truncated division, and modulo) when the other
operand is of the type of `x` and when the signedness of the neutral number must be
preserved to reflect the usual behavior of the binary operation in Julia.

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
