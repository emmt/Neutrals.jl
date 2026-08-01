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

"""
    Neutral.maybe_neutral(x)

If `x` is an `Int` whose value is one of `0`, `1`, or `-1`, return the neutral number
`Neutral{x}()`; otherwise, return `x` unchanged. This is equivalent to:

    x isa Int && x ∈ (0, 1, -1) ? Neutral{x}() : x

!!! note
    This function is not type-stable and is not intended to be efficient. It may be useful
    to encode methods related to the `Neutral` package (metaprogramming) or in tests.

"""
maybe_neutral(x) = x
maybe_neutral(x::Int) =
    x ===  0 ? ZERO :
    x ===  1 ?  ONE :
    x === -1 ? -ONE : x

#----------------------------------------------------------------------------------- Units -
#
# The following methods are replacements of those provided by `Unitful`. They are overridden
# in `ext/NeutralsUnitfulExt.jl` when `Unitful` is loaded.

Base.inv(u::Dimensionless) = u
Base.:(^)(u::Dimensionless, n::Integer) = u
Base.:(*)(::Dimensionless, ::Dimensionless) = Dimensionless()
Base.:(/)(::Dimensionless, ::Dimensionless) = Dimensionless()
Base.:(\)(::Dimensionless, ::Dimensionless) = Dimensionless()
Base.:(*)(x::Number, u::Dimensionless) = x
Base.:(/)(x::Number, u::Dimensionless) = x
Base.:(\)(x::Number, u::Dimensionless) = impl_inv(x)
Base.:(*)(u::Dimensionless, x::Number) = x
Base.:(/)(u::Dimensionless, x::Number) = impl_inv(x)
Base.:(\)(u::Dimensionless, x::Number) = x

"""
    Neutrals.is_dimensionless(x)
    Neutrals.is_dimensionless(typeof(x))

Return whether `x` is dimensionless. This trait may be extended for the type of dimensionful
quantities.

"""
is_dimensionless(x::Number) = is_dimensionless(typeof(x))
is_dimensionless(::Type{<:Real}) = true
is_dimensionless(::Type{<:Complex}) = true
@generated is_dimensionless(::Type{T}) where {T<:Number} = quote
    $(Expr(:meta,:inline))
    return $(isequal(one(T), oneunit(T))::Bool)
end

assert_dimensionless(op::Symbol, x::Number) = assert_dimensionless(op, typeof(x))
assert_dimensionless(op::Symbol, ::Type{T}) where {T} =
    is_dimensionless(T) ? nothing : throw_not_dimensionless(op, T)

@noinline throw_not_dimensionless(op::Symbol, x) = throw(ArgumentError(string(
    "invalid operation `", op,
    "` involving a neutral number and a non-dimensionless number with units ",
    impl_unit(x))))

"""
    Neutrals.impl_unit(x)
    Neutrals.impl_unit(typeof(x))

Return the units of `x`. This trait may be extended for the type of dimensionful quantities.

"""
impl_unit(x::Number) = impl_unit(typeof(x))
impl_unit(::Type{<:Number}) = Dimensionless()

"""
    Neutrals.impl_ustrip(x)
    Neutrals.impl_ustrip(typeof(x))

Return the value of `x` or the type of `x` without units if any. These methods may be
extended for instances and types of dimensionful quantities.

"""
impl_ustrip(x::Number) = x
impl_ustrip(::Type{T}) where {T<:Number} = T

"""
    Neutrals.impl_oneunit(x)
    Neutrals.impl_oneunit(typeof(x))

Return one with the type of `x`, including units if any.

"""
impl_oneunit(x::Number) = impl_oneunit(typeof(x))
impl_oneunit(::Type{T}) where {T<:Number} = oneunit(T)

# There is no `oneunit` for irrational numbers.
impl_oneunit(::Type{T}) where {T<:AbstractIrrational} = 1.0

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

Return the value associated with the neutral number `x`. This *trait* only depends on the
type of `x`.

"""
value(::Neutral{x}) where x = x
value(::Type{<:Neutral{x}}) where x = x

# Conversion rules for bare numeric types. No needs to extend `Base.convert` because
# `Base.convert(T,x)` amounts to evaluating `T(x)::T` for any numeric type `T`.
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
TypeUtils.is_static_number(::Type{<:Neutral}) = true
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
        Base.$f(x::Neutral{V}) where {V} = Neutral{$f(V)}()
    end
end
Base.checked_abs(x::Neutral) = abs(x)
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

"""
    Neutrals.signed_type(T::Type) -> S

Return the signed type `S` that has the same number of bits as `T`.

"""
signed_type(::Type{T}) where {T<:Real} = T
signed_type(::Type{Complex{T}}) where {T} = Complex{signed_type(T)}
signed_type(::Type{Rational{T}}) where {T} = Rational{signed_type(T)}

# NOTE Not all versions of Julia implement `signed(T)`.
for (U, S) in (:UInt8 => :Int8, :UInt16 => :Int16, :UInt32 => :Int32,
               :UInt64 => :Int64, :UInt128 => :Int128)
    if isdefined(Base, U) && isdefined(Base, S)
        @eval signed_type(::Type{$U}) = $S
    end
end

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

#----------------------------------------------------------------------------------- Tests -
#
# The following functions may be used for testing the `Neutral` package or extensions of it.

"""
    using Neutral: ≙
    x ≙ y
    Neutral.strict_isequal(x, y)

Return whether the numbers `x` and `y` have the same type and the same values in the sense
that `isequal(x, y)` is true. This predicate is therefore more strict than `isequal` which
only compare the values, not the types. It may be noticed that `isequal(NaN, NaN)` is true
while `NaN == NaN` is not.

If `x` and `y` are arrays, the call is equivalent to:

    eltype(x) == eltype(y) && axes(x) == axes(y) && all(≙, x, y)

# See also

[`Neutral.sloppy_isequal`](@ref) for a less strict version which consider that two zeros and
two NaNs are equal regardless of their signs.

"""
strict_isequal(x::T, y::T) where {T<:Number} = isequal(x, y)

const ≙ = strict_isequal

"""
    using Neutral: ≗
    x ≗ y
    Neutral.sloppy_isequal(x, y)

Return whether the numbers `x` and `y` have the same type and the same values in the sense
that `isequal(x, y)` is true, or `iszero(x)` and `iszero(y)` are both true, or or `isnan(x)`
and `isnan(y)` are both true. Compared to `isequal`, this amounts to disregarding the signs
or zeros and NaNs when comparing their values.

If `x` and `y` are arrays, the call is equivalent to:

    eltype(x) == eltype(y) && axes(x) == axes(y) && all(≗, x, y)

# See also

[`Neutral.strict_isequal`](@ref) for a more strict version which does not disregard the
signs of zeros and NaNs.

"""
sloppy_isequal(x::T, y::T) where {T<:Number} = isequal(x, y)
sloppy_isequal(x::T, y::T) where {T<:Complex} =
    sloppy_isequal(x.re, y.re) && sloppy_isequal(x.im, y.im)
sloppy_isequal(x::T, y::T) where {T<:AbstractFloat} =
    isequal(x, y) | (iszero(x) & iszero(y)) | (isnan(x) & isnan(y))

const ≗ = sloppy_isequal

for eq in (:strict_isequal, :sloppy_isequal)
    @eval begin
        # Default is false.
        $eq(x::Any, y::Any) = false

        # Implementation for arrays.
        function $eq(x::AbstractArray{T,N}, y::AbstractArray{T,N}) where {T,N}
            axes(x) == axes(y) || return false
            @inbounds for i in eachindex(x, y)
                $eq(x[i], y[i]) || return false
            end
            return true
        end
    end
end
