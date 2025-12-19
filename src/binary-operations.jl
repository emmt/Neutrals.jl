#----------------------------------------------------------------------- Binary operations -

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
#     ==(x::Number, y::Number) in `basae/promotion.jl`
#     <( x::Real, y::Real)     in `basae/promotion.jl`
#     <=(x::Real, y::Real)     in `basae/promotion.jl`
#
# and so on.
#
# Override base methods to call corresponding implementation:
for (f, (g, w, Ts)) in (:(+)   => (:impl_add,    6, (:Number, :Real, :Integer, :Rational,
                                                     :Complex, :(Complex{Bool}), :AbstractIrrational,
                                                     :AbstractFloat, :BigInt, :BigFloat)),
                        :(-)   => (:impl_sub,    3, (:Number, :(Complex{Bool}), :Real, :Integer, :Rational,
                                                     :Complex, :AbstractIrrational,
                                                     :AbstractFloat, :BigInt, :BigFloat)),
                        :(*)   => (:impl_mul,    5, (:Number, :Real, :Integer,
                                                     :Rational, :Complex, :(Complex{Bool}))),
                        :(/)   => (:impl_div,    3, (:Number, :Real, :Integer, :Rational,
                                                     :Complex, :(Complex{Bool}))),
                        :(^)   => (:impl_pow,    2, (:Number, :Real, :Integer, :Rational,
                                                     :(Irrational{:ℯ}),
                                                     :Float16, :Float32, :Float64,
                                                     :(Union{Float16, Float32}), # <- needed to avoid ambiguities with Julia 1.12
                                                     :Complex,
                                                     :(Complex{<:AbstractFloat}),
                                                     :(Complex{<:Integer}),
                                                     :(Complex{<:Rational}),
                                                     :BigInt, :BigFloat)),
                        :div   => (:impl_tdv,    3, (:Real, :Rational)),
                        :rem   => (:impl_rem,    3, (:Real, :Rational)),
                        :mod   => (:impl_mod,    3, (:Real, :Rational)),
                        :(==)  => (:impl_eq,     6, (:Number, :Real, :Rational,
                                                     :AbstractIrrational, :Complex,
                                                     :BigInt, :BigFloat)),
                        :(<)   => (:impl_lt,     3, (:Real, :Rational, :BigInt, :BigFloat)),
                        :(<=)  => (:impl_le,     3, (:Real, :Rational, :BigInt, :BigFloat)),
                        :cmp   => (:impl_cmp,    3, (:Number, :Real, :Integer,
                                                     :BigInt, :BigFloat)),
                        :(|)   => (:impl_or,     6, (:Integer,)),
                        :(&)   => (:impl_and,    6, (:Integer,)),
                        :xor   => (:impl_xor,    6, (:Integer,)),
                        :(<<)  => (:impl_lshft,  2, (:Integer, :Bool)),
                        :(>>)  => (:impl_rshft,  2, (:Integer, :Bool)),
                        :(>>>) => (:impl_urshft, 2, (:Integer, :Bool)),
                        )
    # There is always an implementation when both operands are neutral numbers.
    @eval Base.$f(x::Neutral, y::Neutral) = $g($(Val(3)), x, y)
    for T in Ts
        if (w & 1) == 1
            # Implementation exists when 1st operand is a neutral number.
            @eval Base.$f(x::Neutral, y::$T) = $g($(Val(1)), x, y)
        elseif w == 6
            # Operation is commutative and implementation exists when 2nd operand is a
            # neutral number.
            @eval Base.$f(x::Neutral, y::$T) = $g($(Val(2)), y, x)
        end
        if (w & 2) == 2
            # Implementation exists when 2nd operand is a neutral number.
            @eval Base.$f(x::$T, y::Neutral) = $g($(Val(2)), x, y)
        elseif w == 5
            # Operation is commutative and implementation exists when 1st operand is a
            # neutral number.
            @eval Base.$f(x::$T, y::Neutral) = $g($(Val(1)), y, x)
        end
    end
end

# Encode implementation of some binary operators/functions when both operands are neutral
# numbers. For other binary operators/functions, the base methods are assumed to work thanks
# to the implemented promotion rules.
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
            @eval $g(::Val{3}, ::$(typeof(x)), ::$(typeof(y))) = $r
        elseif r ∈ (0, 1, -1) # returns a neutral number if possible
            @eval $g(::Val{3}, ::$(typeof(x)), ::$(typeof(y))) = $(Neutral{r}())
        else # otherwise returns an integer
            @eval $g(::Val{3}, ::$(typeof(x)), ::$(typeof(y))) = $r
        end
    end

    # Division, modulo, etc.
    for (f, g) in (:(/) => :impl_div,
                   :div => :impl_tdv,
                   :rem => :impl_rem,
                   :mod => :impl_mod)
        if y === ZERO
            @eval $g(::Val{3}, ::$(typeof(x)), ::$(typeof(y))) = throw(DivideError())
        else # y is ONE or -ONE
            r = if f === :(/)
                value(x)*value(y) # x/y yields the same result as x*y when abs(y) = 1
            else
                @eval $f(value($x), value($y))
            end
            @eval $g(::Val{3}, ::$(typeof(x)), ::$(typeof(y))) = $(Neutral{r}())
        end
    end

    # Exponentiation.
    @eval impl_pow(::Val{3}, ::$(typeof(x)), ::$(typeof(y))) = $(y === ZERO ? ONE : x)

    # Comparison.
    @eval impl_cmp(::Val{3}, ::$(typeof(x)), ::$(typeof(y))) = $(cmp(value(x), value(y)))
end

"""
    Neutrals.impl_inv(x) -> 𝟙/x

Implement multiplicative inverse of number `x`. Default to `inv(x)`.

"""
impl_inv(x::Number) = inv(x)
if VERSION < v"1.2.0-rc2"
    # `inv(x)` was not implemented for irrational numbers prior to Julia 1.2.0-rc2
    impl_inv(x::AbstractIrrational) = 1/x
end

"""
    Neutrals.impl_add(w::Val, x, y) -> x + y

Implement addition of numbers `x` and `y` when at least one of the operands is a neutral
number. To avoid ambiguities, the caller must set `w` to `Val(1)` if only `x` is a neutral
number, `Val(2)` if only `y` is a neutral number, and `Val(3)` if `x` and `y` are both
neutral numbers.

This method can be overridden by specializing it when the second operand is a neutral
number, that is for `w::Val{2}`.

"""
impl_add(::Val{2}, x::BareNumber, ::Neutral{0}) = x
impl_add(::Val{2}, x::Number, ::Neutral{ 0}) = is_dimensionless(x) ? x : throw_add_dimensionful_and_zero()
impl_add(::Val{2}, x::Number, ::Neutral{ 1}) = x + convert(type_common(x), 1)
impl_add(::Val{2}, x::Number, ::Neutral{-1}) = x - convert(type_common(x), 1)

@noinline throw_add_dimensionful_and_zero() =
    throw(ArgumentError("𝟘 and dimensionful quantity cannot be added"))

"""
    Neutrals.impl_sub(w::Val, x, y) -> x - y

Implement subtraction of numbers `x` and `y` when at least one of the operands is a neutral
number. See [`Neutrals.impl_add`](@ref) for the interpretation of `w`.

"""
impl_sub(::Val{1}, x::Neutral{ 0}, y::BareNumber) = -y
impl_sub(::Val{1}, x::Neutral{ 0}, y::Number) = is_dimensionless(y) ? -y : throw_sub_dimensionful_and_zero()
impl_sub(::Val{1}, x::Neutral{ 1}, y::Number) = convert(type_common(y), 1) - y
impl_sub(::Val{1}, x::Neutral{-1}, y::Number) = -convert(type_common(y), 1) - y

impl_sub(::Val{2}, x::BareNumber, y::Neutral{0}) = x
impl_sub(::Val{2}, x::Number, y::Neutral{ 0}) = is_dimensionless(x) ? x : throw_sub_dimensionful_and_zero()
impl_sub(::Val{2}, x::Number, y::Neutral{ 1}) = x - convert(type_common(x), 1)
impl_sub(::Val{2}, x::Number, y::Neutral{-1}) = x + convert(type_common(x), 1)

@noinline throw_sub_dimensionful_and_zero() =
    throw(ArgumentError("𝟘 and dimensionful quantity cannot be subtracted"))

# In Julia, Booleans are promoted to `Int` for addition, subtraction and bitwise shifts
# (base/bool.jl). The implementations of addition and subtraction of a Boolean with `±𝟙` are
# specialized according to this.
impl_add(::Val{2}, x::Bool, y::Neutral{ 1}) = Int(x) + 1
impl_add(::Val{2}, x::Bool, y::Neutral{-1}) = Int(x) - 1
#
impl_sub(::Val{2}, x::Bool, y::Neutral{ 1}) = Int(x) - 1
impl_sub(::Val{2}, x::Bool, y::Neutral{-1}) = Int(x) + 1
impl_sub(::Val{1}, x::Neutral{ 1}, y::Bool) = 1 - Int(y)
impl_sub(::Val{1}, x::Neutral{-1}, y::Bool) = -1 - Int(y)

"""
    Neutrals.impl_mul(w::Val, x, y) -> x * y    # if x and y are numbers
    Neutrals.impl_mul(w::Val, x, y) -> x .* y   # if one of x or y is an array

Implemen scalar or element-wise multiplication of `x` by `y` when at least one of the
operands is a neutral number while the other is a number or an array of numbers. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

This method can be overridden by specializing it when the first operand is a neutral number,
that is for `w::Val{1}`.

"""
impl_mul(::Val{1}, x::Neutral{ 0}, y::BareNumber) = ZERO
impl_mul(::Val{1}, x::Neutral{ 0}, y::AbstractArray{<:BareNumber}) = similar(y, typeof(x))
impl_mul(::Val{1}, x::Neutral{ 1}, y::Operand{Number}) = y
impl_mul(::Val{1}, x::Neutral{-1}, y::Operand{Number}) = -y

"""
    Neutrals.impl_div(w::Val, x, y) -> x / y    # if x and y are numbers
    Neutrals.impl_div(w::Val, x, y) -> x ./ y   # if one of x or y is an array

Implement scalar or element-wise division of `x` by `y` when at least one of the operands is
a neutral number while the other is a number or an array of numbers. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

"""
impl_div(::Val{1}, x::Neutral{ 0}, y::BareNumber) = ZERO
impl_div(::Val{1}, x::Neutral{ 1}, y::Number) = impl_inv(y)
impl_div(::Val{1}, x::Neutral{-1}, y::Number) = -impl_inv(y)

impl_div(::Val{2}, x::Operand{Number}, y::Neutral{0}) = throw(DivideError())
impl_div(::Val{2}, x::Operand{Number}, y::Neutral{1}) = x
impl_div(::Val{2}, x::Operand{Number}, y::Neutral{-1}) = -x

# Element-wise division of neutral number `x` by array `y`. Division by zero is first
# checked, then the result is computed according to the specific value of `x` using
# auxiliary function `_impl_div` to dispatch on `x`.
impl_div(::Val{1}, x::Neutral, y::AbstractArray{<:Neutral{0}}) = throw(DivideError())
impl_div(::Val{1}, x::Neutral, y::AbstractArray{<:Number}) = _impl_div(x, y) # to dispatch on x
_impl_div(x::Neutral{ 0}, y::AbstractArray{<:BareNumber}) = similar(y, typeof(x))
_impl_div(x::Neutral{ 1}, y::AbstractArray{<:Number}) = impl_inv.(y)
_impl_div(x::Neutral{-1}, y::AbstractArray{<:Number}) = -impl_inv.(y)

"""
    Neutrals.impl_tdv(w::Val, x, y) -> x ÷ y

Implement the truncated division of `x` by `y` that is the quotient of `x` by `y` rounded
toward zero. This corresponds to `div(x,y,RoundToZero)`. See [`Neutrals.impl_add`](@ref) for
the interpretation of `w`.

""" impl_tdv

"""
    Neutrals.impl_rem(w::Val, x, y) -> rem(x, y)

Implement the remainder function when at least one of the operands is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

The remainder function satisfies `x == div(x,y)*y + rem(x,y)` with `div` the truncated
division which yields the quotient rounded toward zero, implying that sign matches `x`.

"""
impl_rem

"""
    Neutrals.impl_mod(w::Val, x, y) -> mod(x, y)

Implement `mod` when at least one of the operands is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

The modulus function satisfies `x == fld(x,y)*y + mod(x,y)`, with `fld` the floored division
which yields the rounded towards `-Inf`, implying that sign matches `y`.

""" impl_mod

# In Julia, `div` and `rem` yield a result of the signedness of the 1st operand, while
# `mod` yields a result of the signedness of the 2nd operand. For these operations, a
# neutral number is thus converted to a signed value whose type is based on that of the
# other operand.
for (f, g) in (:div => :impl_tdv, :rem => :impl_rem, :mod => :impl_mod)
    @eval begin
        $g(::Val{2}, x::Real, y::Neutral{0}) = throw(DivideError())
        $g(::Val{2}, x::Real, y::Neutral) = $f(x, convert(type_signed(x), y))
        $g(::Val{1}, x::Neutral, y::Real) = $f(convert(type_signed(y), x), y)
    end
end

# Specialize implementation for integers (not Booleans) and for `±𝟙` considering that
# neutral numbers are signed integers.
#
# Quotient of truncated division is of the signedness of the 1st operand.
impl_tdv(::Val{2}, x::Integer, y::Neutral{1}) = x
#
# Remainder of truncated division is of the signedness of the `st operand.
impl_rem(::Val{2}, x::Integer, y::Neutral{1}) = zero(x) # FIXME yield ZERO instead?
impl_rem(::Val{2}, x::Signed, y::Neutral{-1}) = zero(x) # FIXME yield ZERO instead?
#
# Modulo is of the signedness of the 2nd operand and is 0 if 2nd operand is -1.
impl_mod(::Val{2}, x::Integer, y::Neutral{1}) = zero(type_signed(x)) # FIXME yield ZERO instead?
impl_mod(::Val{2}, x::Integer, y::Neutral{-1}) = zero(type_signed(x)) # FIXME yield ZERO instead?
#
# For Booleans, implementation of `div`, `rem`, and `mod` in `base/bool.jl` is:
#
#     div(x::Bool, y::Bool) = y ? x : throw(DivideError())
#     rem(x::Bool, y::Bool) = y ? false : throw(DivideError())
#     mod(x::Bool, y::Bool) = rem(x,y)
#
impl_tdv(::Val{2}, x::Bool, y::Neutral{1}) = x
impl_rem(::Val{2}, x::Bool, y::Neutral{1}) = false
impl_mod(::Val{2}, x::Bool, y::Neutral{1}) = false
for f in (:impl_tdv, :impl_rem, :impl_mod)
    @eval $f(::Val{2}, x::Bool, y::Neutral{-1}) = throw(InexactError(:convert, Bool, -ONE))
end

"""
    Neutrals.impl_pow(w::Val, x, y) -> x^y

Implements raising number `x` to the power `y` when `y` is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

"""
impl_pow(::Val{2}, x::Number, ::Neutral{0}) = oneunit(x)
impl_pow(::Val{2}, x::Number, ::Neutral{1}) = x
impl_pow(::Val{2}, x::Number, ::Neutral{-1}) = impl_inv(x)

# There is no `oneunit` for irrational numbers.
impl_pow(::Val{2}, x::AbstractIrrational, ::Neutral{0}) = 1.0

"""
    Neutrals.impl_eq(w::Val, x, y) -> x == y

Implements `==` for numbers when at least one of the operands is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

This method can be overridden by specializing it when the second operand is a neutral
number, that is for for `w::Val{2}`.

"""
impl_eq(::Val{2}, x::Number, ::Neutral{ 0}) = is_dimensionless(x) && iszero(x)
impl_eq(::Val{2}, x::Number, ::Neutral{ 1}) = isone(x)
impl_eq(::Val{2}, x::Number, ::Neutral{-1}) = x == -convert(type_common(x), 1)
 # NOTE We are assuming that `isone(x)` is not slower than `x == one(x)` or `x ==
 #      convert(type_common(x), 1)`. We assume that `x == -𝟙` is specialized to yield
 #      `false` for unsigned numbers (see below).

# Optimize comparison of an unsigned real and a neutral number.
impl_eq(::Val{2}, x::UnsignedNumber, y::Neutral{-1}) = false
#
impl_eq(::Val{2}, x::Bool, y::Neutral{1}) = x
impl_eq(::Val{2}, x::Bool, y::Neutral{0}) = !x

# Neutral numbers are integers and are never equal to irrational numbers.
for n in instances(Neutral)
    @eval impl_eq(::Val{2}, x::AbstractIrrational, y::$(typeof(n))) = false
end

"""
    Neutrals.impl_lt(w::Val, x, y) -> x < y

Implement `<` for real numbers when at least one of the operands is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

""" impl_lt

# Optimize comparison of an unsigned real and a neutral number.
impl_lt(::Val{2}, x::UnsignedReal, y::Neutral{0}) = false
impl_lt(::Val{2}, x::UnsignedReal, y::Neutral{-1}) = false
impl_lt(::Val{1}, x::Neutral{-1}, y::UnsignedReal) = true
#
impl_lt(::Val{2}, x::Bool, y::Neutral{1}) = !x
impl_lt(::Val{1}, x::Neutral{0}, y::Bool) = y
impl_lt(::Val{1}, x::Neutral{1}, y::Bool) = false

"""
    Neutrals.impl_le(w::Val, x, y) -> x ≤ y

Implement `≤` for real numbers when at least one of the operands is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

""" impl_le

# Optimize comparison of an unsigned real and a neutral number.
impl_le(::Val{2}, x::UnsignedReal, y::Neutral{-1}) = false
impl_le(::Val{1}, x::Neutral{0}, y::UnsignedReal) = true
impl_le(::Val{1}, x::Neutral{-1}, y::UnsignedReal) = true
#
impl_le(::Val{2}, x::Bool, y::Neutral{0}) = !x
impl_le(::Val{2}, x::Bool, y::Neutral{1}) = true
impl_le(::Val{1}, x::Neutral{1}, y::Bool) = y

for (f, g) in (:(<) => :impl_lt, :(<=) => :impl_le)
    @eval begin
        $g(::Val{2}, x::Real, y::Neutral) = $f(x, convert(type_common(x), y))
        $g(::Val{1}, x::Neutral, y::Real) = $f(convert(type_common(y), x), y)
    end
end

"""
    Neutrals.impl_cmp(w::Val, x, y) -> cmp(x, y)

Implement `cmp` for real numbers when at least one of the operands is a neutral number. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

This method can be overridden by specializing it when the second operand is a neutral
number.

"""
impl_cmp(::Val{1}, x::Neutral, y::Real) =
    -impl_cmp(Val(2), y, x) # put neutral number second
impl_cmp(::Val{2}, x::Integer, y::Neutral) =
    ifelse(impl_isless(Val(2), x, y), -1, ifelse(impl_isless(Val(1), y, x), 1, 0))
impl_cmp(::Val{2}, x::Real, y::Neutral) =
    impl_isless(Val(2), x, y) ? -1 : ifelse(impl_isless(Val(1), y, x), 1, 0)

# Optimize comparison of an unsigned real and a neutral number.
impl_cmp(::Val{2}, x::UnsignedReal, y::Neutral{-1}) = 1
impl_cmp(::Val{2}, x::UnsignedReal, y::Neutral{0}) = iszero(x) ? 0 : 1
#
impl_cmp(::Val{2}, x::Bool, y::Neutral{1}) = x ? 0 : -1

"""
    Neutrals.impl_isless(w::Val, x, y) -> isless(x, y)

Implement `isless` for real numbers when at least one of the operands is a neutral number.
See [`Neutrals.impl_add`](@ref) for the interpretation of `w`.

"""
@inline impl_isless(w::Val, x::Real, y::Real) = impl_lt(w, x, y)

# NOTE For floats in `base/float.jl`:
#      isless(x, y) =  isnan(x) || isnan(b) ? !isnan(x) : x < y
@inline impl_isless(::Val{2}, x::AbstractFloat, y::Neutral) =
    isnan(x) ? false : x < oftype(x, value(y))
@inline impl_isless(::Val{1}, x::Neutral, y::AbstractFloat) =
    isnan(y) ? true : oftype(y, value(x)) < y

# For bitwise operations (`|`, `&`, and `xor`) between integers (including Booleans and big
# integers) of mixed types, the called methods are defined in `base/int.jl` and promote
# their arguments before calling a more specialized method. When one operand is a neutral
# number, we override this method to implement optimized expressions. Even though the other
# operand is unsigned, we consider that `-𝟙` behaves as a constant of the same type with all
# its bits set to 1.

"""
    Neutrals.impl_or(w::Val, x, y) -> x | y

Implement `x | y` when one of the operands is a neutral number while the other is an
integer. See [`Neutrals.impl_add`](@ref) for the interpretation of `w`. If this method is
overridden, it is sufficient to specialize it when the second operand is a neutral number,
that is for `w::Val{2}`.

"""
impl_or(::Val{2}, x::Integer, ::Neutral{0}) = x
impl_or(::Val{2}, x::Integer, ::Neutral{1}) = x | one(x)
impl_or(::Val{2}, x::Integer, ::Neutral{-1}) = ~zero(x) # NOTE see remark for `x & 𝟘`

# Optimize for Booleans.
impl_or(::Val{2}, x::Bool, ::Neutral{1}) = true
impl_or(::Val{2}, x::Bool, ::Neutral{-1}) = true

"""
    Neutrals.impl_and(w::Val, x, y) -> x & y

Implement `x & y` when one of the operands is a neutral number while the other is an
integer. See [`Neutrals.impl_add`](@ref) for the interpretation of `w`. If this method is
overridden, it is sufficient to specialize it when the second operand is a neutral number,
that is for `w::Val{2}`.

"""
impl_and(::Val{2}, x::Integer, ::Neutral{0}) = zero(x) # NOTE not 𝟘, because 𝟘 is defined according to + and *, not &
impl_and(::Val{2}, x::Integer, ::Neutral{1}) = x & one(x)
impl_and(::Val{2}, x::Integer, ::Neutral{-1}) = x

# Optimize for Booleans.
impl_and(::Val{2}, x::Bool, ::Neutral{1}) = x

"""
    Neutrals.impl_xor(w::Val, x, y)

Implement `xor(x, y)` when one of the operands is a neutral number while the other is an
integer. See [`Neutrals.impl_add`](@ref) for the interpretation of `w`. If this method is
overridden, it is sufficient to specialize it when the second operand is a neutral number,
that is for `w::Val{2}`.

"""
impl_xor(::Val{2}, x::Integer, y::Neutral{0}) = x
impl_xor(::Val{2}, x::Integer, y::Neutral{1}) = xor(x, one(x))
impl_xor(::Val{2}, x::Integer, y::Neutral{-1}) = xor(x, ~zero(x))

# Optimize for Booleans.
impl_xor(::Val{2}, x::Bool, ::Neutral{1}) = !x
impl_xor(::Val{2}, x::Bool, ::Neutral{-1}) = !x

# For bit shift operation of an integer `x` (including Booleans and big integers) by a
# number of bits specified by a neutral number, it is sufficient to override the
# corresponding base methods (in `base/operators.jl`) whose left operand is an `Integer` and
# the right one is an `Int` to yield either `x` (if shifting by 𝟘) or to call the right
# operation with a number of bits specified as an `UInt` (see base/int.jl).

"""
    Neutrals.impl_lshft(w::Val{2}, x, y) -> x << y

Implement left bit shift of integer `x` by neutral number `y`. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

"""
impl_lshft(::Val{2}, x::Integer, ::Neutral{ 0}) = x
impl_lshft(::Val{2}, x::Integer, ::Neutral{ 1}) = x << UInt(1)
impl_lshft(::Val{2}, x::Integer, ::Neutral{-1}) = x >> UInt(1)

"""
    Neutrals.impl_rshft(w::Val{2}, x, y) -> x >> y

Implement right bit shift of integer `x` by neutral number `y`. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

"""
impl_rshft(::Val{2}, x::Integer, ::Neutral{ 0}) = x
impl_rshft(::Val{2}, x::Integer, ::Neutral{ 1}) = x >> UInt(1)
impl_rshft(::Val{2}, x::Integer, ::Neutral{-1}) = x << UInt(1)

"""
    Neutrals.impl_rshft(w::Val{2}, x, y) -> x >>> y

Implement unsigned right bit shift of integer `x` by neutral number `y`. See
[`Neutrals.impl_add`](@ref) for the interpretation of `w`.

"""
impl_urshft(::Val{2}, x::Integer, ::Neutral{ 0}) = x
impl_urshft(::Val{2}, x::Integer, ::Neutral{ 1}) = x >>> UInt(1)
impl_urshft(::Val{2}, x::Integer, ::Neutral{-1}) = x << UInt(1)

#----------------------------------------------------------------------------- Big numbers -
#
# As can be seen in `base/gmp.jl` and `base/mpfr.jl`, the result of a comparison with `==`,
# `<`, or `<=` between a big number and a non-big number is given by `cmp`. So there are no
# needs to specialize `==`, `<`, and `<=` to handle these cases, only `cmp` may be
# specialized. For big floats, `cmp` converts the non-big operand to a big float so there
# nothing to do here. For big integers, `cmp` with a non-big integer `c` of size not larger
# than a `Clong` calls one of the compiled methods with `c` as a `Clong` or as a `Culong`.
# Hence, we only have to specialize `cmp` for a big integer and a neutral number.
impl_cmp(::Val{2}, x::BigInt, y::Neutral{ 0}) = cmp(x, Culong(0))
impl_cmp(::Val{2}, x::BigInt, y::Neutral{ 1}) = cmp(x, Culong(1))
impl_cmp(::Val{2}, x::BigInt, y::Neutral{-1}) = cmp(x, Clong(-1))
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
        impl_add(::Val{2}, x::$T, y::Neutral{ 1}) = x + Culong(1)
        impl_add(::Val{2}, x::$T, y::Neutral{-1}) = x - Culong(1)

        # Subtraction. It is only needed to extend the rules for `±𝟙`.
        impl_sub(::Val{2}, x::$T, y::Neutral{ 1}) = x - Culong(1)
        impl_sub(::Val{2}, x::$T, y::Neutral{-1}) = x + Culong(1)

        impl_sub(::Val{1}, x::Neutral{ 1}, y::$T) = Culong(1) - y
        impl_sub(::Val{1}, x::Neutral{-1}, y::$T) = -(y + Culong(1))

        # Equality. It is only needed to extend the rules for `-𝟙`.
        impl_eq(::Val{2}, x::$T, y::Neutral{-1}) = x == Clong(-1)
    end
end

#---------------------------------------------------------------------------- Broadcasting -
#
# For broadcasted operations like `x .+ 𝟙` the existing rules yield a result which is stored
# into a new array and which is as fast to compute as would a specialized method. We
# specialize the few broadcasted operations, like `x .+ 𝟘` that could yield `x` unchanged or
# a result like `x .* 𝟘` to yield an array of `𝟘`s without computations.

# Base method to extend for broadcasted operations.
import Base.Broadcast: broadcasted

# Commutative operations which can yield `x` for a specific neutral number..
for (op, n, T) in ((:+,    0, Number),
                   (:|,    0, Integer),
                   (:&,   -1, Integer),
                   (:xor,  0, Integer))
    @eval begin
        broadcasted(::typeof($op), x::Neutral{$n}, ::Neutral{$n}) = x
        broadcasted(::typeof($op), x::Operand{$T}, ::Neutral{$n}) = x
        broadcasted(::typeof($op), ::Neutral{$n}, x::Operand{$T}) = x
    end
end

broadcasted(::typeof(-), x::Operand{Number}, ::Neutral{0}) = x

broadcasted(::typeof(*), x::Neutral, y::Neutral) = impl_mul(Val(3), x, y)
broadcasted(::typeof(*), x::Operand{Number}, y::Neutral) = impl_mul(Val(1), y, x) # put neutral number 1st
broadcasted(::typeof(*), x::Neutral, y::Operand{Number}) = impl_mul(Val(1), x, y)

broadcasted(::typeof(/), x::Neutral, y::Neutral) = impl_div(Val(3), x, y)
broadcasted(::typeof(/), x::Operand{Number}, y::Neutral) = impl_div(Val(2), x, y)
broadcasted(::typeof(/), x::Neutral, y::Operand{Number}) = impl_div(Val(1), x, y)

broadcasted(::typeof(\), x::Neutral, y::Neutral) = broadcasted(/, y, x)
broadcasted(::typeof(\), x::Neutral, y::Operand{Number}) = broadcasted(/, y, x)
broadcasted(::typeof(\), x::Operand{Number}, y::Neutral) = broadcasted(/, y, x)

broadcasted(::typeof(^), x::Operand{Number}, ::Neutral{1}) = x

broadcasted(::typeof(div), x::Operand{Integer}, ::Neutral{1}) = x

broadcasted(::typeof(<<),  x::Operand{Integer}, ::Neutral{0}) = x
broadcasted(::typeof(>>),  x::Operand{Integer}, ::Neutral{0}) = x
broadcasted(::typeof(>>>), x::Operand{Integer}, ::Neutral{0}) = x

# This one is special (as usual with Booleans...).
broadcasted(::typeof(&), ::Neutral{1}, x::Operand{Bool}) = x
broadcasted(::typeof(&), x::Operand{Bool}, ::Neutral{1}) = x

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
