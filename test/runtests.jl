module TestingNeutrals

using Neutrals
using Test
using TypeUtils
using Unitful, Unitful.DefaultSymbols

using Base: Fix1, Fix2

struct LengthInMeters{T<:Real} <: Number
    len::T
end

const UnsignedRational = Rational{<:Union{Bool,Unsigned}}
const UnsignedReal = Union{Bool,Unsigned,UnsignedRational}
const UnsignedComplex = Complex{<:UnsignedReal}

Neutrals.is_dimensionless(::Type{<:LengthInMeters}) = false
Base.zero(::Type{LengthInMeters{T}}) where {T} = LengthInMeters(zero(T))
Base.one(::Type{LengthInMeters{T}}) where {T} = one(T)
Base.oneunit(::Type{LengthInMeters{T}}) where {T} = LengthInMeters(oneunit(T))
Base.:-(x::LengthInMeters) = DimensionlessNumber(-x.val)

struct DimensionlessNumber{T<:Real} <: Number
    val::T
end

Neutrals.is_dimensionless(::Type{<:DimensionlessNumber}) = true
Base.zero(::Type{DimensionlessNumber{T}}) where {T} = DimensionlessNumber(zero(T))
Base.one(::Type{DimensionlessNumber{T}}) where {T} = DimensionlessNumber(one(T))
Base.oneunit(::Type{DimensionlessNumber{T}}) where {T} = DimensionlessNumber(oneunit(T))
Base.:-(x::DimensionlessNumber) = DimensionlessNumber(-x.val)
Base.:inv(x::DimensionlessNumber) = DimensionlessNumber(inv(x.val))

# Fix inv(x), one(x), zero(x), etc. for irrational numbers for old Julia versions.
for f in (:inv, :zero, :one, :oneunit)
     # Use base version by default.
    @eval @inline $f(args...; kwds...) = Base.$f(args...; kwds...)
end
if VERSION < v"1.2.0-rc2"
    inv(x::AbstractIrrational) = 1/x
end
if VERSION < v"1.5.0-rc1"
    zero(::AbstractIrrational) = false
    zero(::Type{<:AbstractIrrational}) = false
    one(::AbstractIrrational) = true
    one(::Type{<:AbstractIrrational}) = true
end
oneunit(::AbstractIrrational) = true
oneunit(::Type{<:AbstractIrrational}) = true

maybe(::Type{Neutral}, x::Integer) = (-1 ≤ x ≤ 1 ? Neutral(x) : x)

storage_type(::Type{T}) where {T<:Real} = T
storage_type(::Type{Complex{T}}) where {T} = storage_type(T)
storage_type(::Type{Rational{T}}) where {T} = T

signed_type(::Type{T}) where {T<:Real} = T
signed_type(::Type{Complex{T}}) where {T} = Complex{signed_type(T)}
signed_type(::Type{Rational{T}}) where {T} = Rational{signed_type(T)}
# NOTE Not all versions of Julia implement `signed(T)`.
for (U, S) in (:UInt8 => :Int8, :UInt16 => :Int16, :UInt32 => :Int32,
               :UInt64 => :Int64, :UInt128 => :Int128)
    @eval signed_type(::Type{$U}) = $S
end

@testset "Neutrals.jl" begin
    types = (Integer,
             Bool,
             Int8, Int16, Int32, Int64, Int128, BigInt,
             UInt8, UInt16, UInt32, UInt64, UInt128,
             AbstractFloat,
             Float16, Float32, Float64, BigFloat,
             Rational, Rational{Bool}, Rational{Int8}, Rational{UInt8},
             Complex{Bool}, Complex{Int16}, Complex{UInt16}, Complex{Float32})
    #integers = filter(T -> T <: Integer, collect(types))
    #floats = filter(T -> T <: AbstractFloat, collect(types))
    others = (true, false,
              0x0, 0x1, 0x5,
              0, 1, -1, 2, 7, -6,
              0x00//0x01, 0x01//0x01, 0x01//0x03,
              0//1, 1//1, -1//1, -1//2,
              0.0f0, 1.0f0, -1.0f0, 2.0f0, Inf32, -Inf32, NaN32,
              0.0, 1.0, -1.0, 0.4, Inf, -Inf, NaN, -NaN,
              π,
              0 + 0im, 1.0 - 2.0im, complex(-1//1, 3//1), #= FIXME complex(pi, pi), =#
              BigInt(0), BigInt(1), BigInt(-1), BigInt(3),
              BigFloat(0), BigFloat(1), BigFloat(-1), BigFloat(3))
    numbers = (instances(Neutral)..., others...)

    # Check assumptions made about how Julia treats ordinary numbers.
    @testset "Assumptions" begin
        # 0 and 1 are representable for any integer type.
        @test Bool(0) === zero(Bool)
        @test Bool(0) === (0 % Bool)
        @test Bool(1) === one(Bool)
        @test Bool(1) === (1 % Bool)
        @test Int8(0) === zero(Int8)
        @test Int8(0) === (0 % Int8)
        @test Int8(1) === one(Int8)
        @test Int8(1) === (1 % Int8)
        @test UInt8(0) === zero(UInt8)
        @test UInt8(0) === (0 % UInt8)
        @test UInt8(1) === one(UInt8)
        @test UInt8(1) === (1 % UInt8)
        @test Int128(0) === zero(Int128)
        @test Int128(0) === (0 % Int128)
        @test Int128(1) === one(Int128)
        @test Int128(1) === (1 % Int128)
        @test UInt128(0) === zero(UInt128)
        @test UInt128(0) === (0 % UInt128)
        @test UInt128(1) === one(UInt128)
        @test UInt128(1) === (1 % UInt128)
        @test BigInt(0) == zero(BigInt)
        @test BigInt(0) == (0 % BigInt)
        @test BigInt(1) == one(BigInt)
        @test BigInt(1) == (1 % BigInt)

        # For signed integers, -1 is representable, not for unsigned ones. For integer
        # type `T`, `((-1) % T)`, `-one(T)`, and `~zero(T)` are the same thing.
        @test_throws InexactError Bool(-1)
        @test -one(Bool) === -1 # Bool differently here
        @test ((-1) % Bool) === true
        @test ((-1) % Bool) === ~zero(Bool)
        #
        @test ((-1) % Int8) === Int8(-1)
        @test ((-1) % Int8) === -one(Int8)
        @test ((-1) % Int8) === ~zero(Int8)
        #
        @test_throws InexactError UInt8(-1)
        @test ((-1) % UInt8) === -one(UInt8)
        @test ((-1) % UInt8) === ~zero(UInt8)
        #
        @test ((-1) % Int128) === Int128(-1)
        @test ((-1) % Int128) === -Int128(1)
        @test ((-1) % Int128) === ~zero(Int128)
        #
        @test_throws InexactError UInt128(-1)
        @test ((-1) % UInt128) === -one(UInt128)
        @test ((-1) % UInt128) === ~zero(UInt128)
        #
        @test ((-1) % BigInt) == BigInt(-1)
        @test ((-1) % BigInt) == -BigInt(1)
        @test ((-1) % BigInt) == ~zero(BigInt)

        # Optimization for rem(x, 𝟙) and mod(x, 𝟙) when x is an integer.
        @testset "`$f(x, one(x)) == zero(x)` for `typeof(x) = $T`" for f in (rem, mod), T in (Bool, Int8, UInt8)
            @test all(iszero, (f(x, one(x)) for x in typemin(T):typemax(T)))
        end

        # Optimization for rem(x, -𝟙) and mod(x, -𝟙) when x is a signed integer.
        @testset "`$f(x, one(x)) == zero(x)` for `typeof(x) = $T`" for f in (rem, mod), T in (Bool, Int8, UInt8)
            @test all(iszero, (f(x, one(x)) for x in typemin(T):typemax(T)))
        end
        @test all(iszero, (rem(x, -one(x)) for x in typemin(Int8):typemax(Int8)))
        @test all(iszero, (mod(x, -one(x)) for x in typemin(Int8):typemax(Int8)))

        # Negating unsigned integers and complexes with unsigned integer parts
        # is possible.
        @test -(0x00) === 0x00
        @test -(0x01) === 0xff
        @test -(0xff) === 0x01
        @test -complex(0x00, 0x00) === complex(-0x00,-0x00)
        @test -complex(0x01, 0xff) === complex(-0x01,-0xff)

        # Negating rationals with unsigned parts is forbidden.
        @test_throws OverflowError -(0x01//0x01)

        # Arithmetic operations combining an ordinary real and an irrational number yield
        # Float64.
        @test typeof(pi + 1) == Float64
    end

    @testset "Neutral type and instances" begin
        @test length(instances(Neutral)) == 3
        @test_throws Exception Neutral(-2)
        @test_throws Exception Neutral("1")
        @test repr(ZERO) == "𝟘"
        @test repr(ONE) == "𝟙"
        @test repr(-ONE) == "-𝟙"
        if VERSION ≥ v"1.3"
            @test ZERO === eval(Meta.parse("𝟘"))
            @test ONE === eval(Meta.parse("𝟙"))
            @test -ONE === eval(Meta.parse("-𝟙"))
        end
        @test typemin(Neutral) === -ONE
        @test typemax(Neutral) === ONE
        @test zero(Neutral) === ZERO
        @test one(Neutral) === ONE
    end

    @testset "Constructors of $x" for (v, x) in (0 => ZERO, 1 => ONE, -1 => -ONE)
        # Consistency.
        @test x ∈ instances(Neutral)
        @test Int(x) === v
        @test Neutrals.value(x) === v
        @test Neutrals.value(typeof(x)) === v

        # Constructors.
        @test Neutral{v}() === x
        @test Neutral(v) === x
        @test Neutral(x) === x
        @test Neutral{v}(x) === x
        @test Neutral(Int8(v)) === x
        @test Neutral{v}(Int8(v)) === x
        @test Neutral(float(v)) === x
        @test Neutral{v}(float(v)) === x
        @test_throws Exception Neutral{Int8(v)}()
        for o in instances(Neutral)
            o === x && continue
            @test_throws InexactError typeof(x)(o)
        end

        # Conversion.
        @test convert(typeof(x), x) === x
        @test convert(Neutral, x) === x
        @test typeof(x)(x) === x
        @test convert(Integer, x) === x
        @test Integer(x) === x
        @test Number(x) === x
        @test Real(x) === x
        @test AbstractFloat(x) === float(Int(x))
        @test Rational(x) === Int(x)//1
        @test Complex(x) === Int(x) + 0im
        @test_throws InexactError AbstractIrrational(x)
    end

    @testset "Unary functions of $x" for x in instances(Neutral)
        @test summary(x) isa String
        @test repr(x) isa String
        @test +x === x
        @test -x === Neutral(-Int(x))
        @test ~x === maybe(Neutral, ~Int(x))
        @test typemin(x) === x
        @test typemax(x) === x
        @test iszero(x) == iszero(Int(x))
        @test isone(x) == isone(Int(x))
        @test isfinite(x) == true
        @test sign(x) === sign(Int(x))
        @test signbit(x) === signbit(Int(x))
        @test abs(x) === Neutral(abs(Int(x)))
        @test abs2(x) === Neutral(abs2(Int(x)))
        @test conj(x) === x
        @test transpose(x) === x
        @test adjoint(x) === x
        @test zero(x) === ZERO
        @test one(x) === ONE
        @test angle(x) === (Int(x) == -1 ? π : ZERO)
        if iszero(x)
            @test_throws DivideError inv(x)
        else
            @test inv(x) === x
        end
        @test iseven(x) === iseven(Int(x))
        @test isodd(x) === isodd(Int(x))
        @test is_signed(x)
        @test is_signed(typeof(x))
    end

    @testset "Conversion of $x to type $T" for T in types, x in instances(Neutral)
        # `convert(T,x)` and `T(x)` should yield the same result equal to `T(value(x))`
        # except if `x` is `-ONE` and `T` is unsigned in which case an `InexactError`
        # exception is thrown.
        if is_signed(T) || Int(x) ≥ 0
            y = @inferred T(x)
            @test y isa T
            @test y == T(Int(x))
            if VERSION < v"1.1"
                # For some reasons this inference is broken in tests with Julia 1.0.
                z = convert(T, x)
            else
                z = @inferred convert(T, x)
            end
            @test typeof(z) == typeof(y)
            @test z == y
            if T === AbstractFloat
                @test y isa Float64
                @test y === float(x)
            end
        else
            @test_throws InexactError T(x)
            @test_throws InexactError convert(T, x)
        end
        if T <: Integer
            y = @inferred rem(x, T)
            @test y isa T
            @test y == (Int(x) % T)
        end
    end

    @testset "Promote rules" begin
        @test promote(true,  ZERO) === (true,  false)
        @test promote(false, ZERO) === (false, false)
        @test promote(true,   ONE) === (true,  true)
        @test promote(false,  ONE) === (false, true)
        @test promote(true,  -ONE) === (1, -1)
        @test promote(false, -ONE) === (0, -1)
        @test promote(ZERO, ZERO) === (ZERO, ZERO)
        @test promote(ZERO,  ONE) === (0, 1)
        @test promote(ZERO, -ONE) === (0, -1)
        @test promote(ZERO, -3.0f0) === (0.0f0, -3.0f0)
        @test promote(ZERO,  pi) === (0.0, float(pi))
        @test promote( ONE, ZERO) === (1, 0)
        @test promote( ONE,  ONE) === (ONE, ONE)
        @test promote( ONE, -ONE) === (1, -1)
        @test promote(-ONE, ZERO) === (-1, 0)
        @test promote(-ONE,  ONE) === (-1, 1)
        @test promote(-ONE, -ONE) === (-ONE, -ONE)

        @testset "Neutrals.type_common($T)" for T in (Int8, UInt8, Int16, UInt16,
                                                      Int32, UInt32, Int64, UInt64,
                                                      Int128, UInt128, BigInt,
                                                      Float16, Float32, Float64, BigFloat,
                                                      typeof(pi),
                                                      Rational{UInt8}, Rational{Int},
                                                      Complex{Float32}, Complex{Rational{Int16}},
                                                      Complex{Rational{UInt32}})
            S = T <: AbstractIrrational ? Float64 :
                T <: Union{BigInt,BigFloat} ? Clong : storage_type(T)
            @test Neutrals.type_common(T) === S
        end
        @testset "Neutrals.type_signed($T)" for T in (Int8, UInt8, Int16, UInt16,
                                                      Int32, UInt32, Int64, UInt64,
                                                      Int128, UInt128, BigInt,
                                                      Float16, Float32, Float64, BigFloat,
                                                      typeof(pi),
                                                      Rational{UInt8}, Rational{Int},
                                                      Complex{Float32}, Complex{Rational{Int16}},
                                                      Complex{Rational{UInt32}})
            S = T <: AbstractIrrational ? Float64 : storage_type(T)
            S = S <: Unsigned ? signed_type(S) : S
            @test Neutrals.type_signed(T) === S
        end
    end

    @testset "Binary operations between $x and $y" for x in instances(Neutral), y in instances(Neutral)
        # Comparisons.
        @test (x == y) === (Int(x) == Int(y))
        @test (x != y) === (Int(x) != Int(y))
        @test (x < y) === (Int(x) < Int(y))
        @test (x > y) === (Int(x) > Int(y))
        @test (x ≤ y) === (Int(x) ≤ Int(y))
        @test (x ≥ y) === (Int(x) ≥ Int(y))
        @test isequal(x, y) === isequal(Int(x), Int(y))
        @test isless(x, y) === isless(Int(x), Int(y))
        @test cmp(x, y) === cmp(Int(x), Int(y))

        # Arithmetic.
        @test (x + y) === maybe(Neutral, Int(x) + Int(y))
        @test (x - y) === maybe(Neutral, Int(x) - Int(y))
        @test (x * y) === maybe(Neutral, Int(x) * Int(y))
        @test (x | y) === maybe(Neutral, Int(x) | Int(y))
        @test (x & y) === maybe(Neutral, Int(x) & Int(y))
        @test xor(x, y) === maybe(Neutral, xor(Int(x), Int(y)))
        @test (x << y) === maybe(Neutral, Int(x) << Int(y))
        @test (x >> y) === maybe(Neutral, Int(x) >> Int(y))
        @test (x >>> y) === maybe(Neutral, Int(x) >>> Int(y))
        if iszero(y)
            @test (x ^ y) === ONE
            @test_throws DivideError x / y
            @test_throws DivideError div(x, y)
            @test_throws DivideError rem(x, y)
            @test_throws DivideError mod(x, y)
        else
            @test (x ^ y) === x
            @test (x / y) === maybe(Neutral, Int(Int(x) / Int(y)))
            @test div(x, y) === maybe(Neutral, div(Int(x), Int(y)))
            @test rem(x, y) === maybe(Neutral, rem(Int(x), Int(y)))
            @test mod(x, y) === maybe(Neutral, mod(Int(x), Int(y)))
        end
    end

    @testset "Arithmetic operations with $x" for x in others
        # Addition and subtraction with ZERO, the neutral element for the addition of
        # numbers.
        @test ZERO + x === x
        @test x + ZERO === x
        @test x - ZERO === x
        if !(x isa Rational{<:Unsigned})
            @test isequal(ZERO - x, -x)
        end

        # Multiplication and division by ONE, the neutral element for the multiplication
        # of numbers.
        @test ONE*x === x
        @test x*ONE === x
        @test ONE\x === x
        @test x/ONE === x
        @test isequal(ONE/x, inv(x))
        @test isequal(x\ONE, inv(x))

        # Multiplication and division by ZERO, a strong zero for the multiplication of
        # numbers.
        @test ZERO*x === ZERO
        @test x*ZERO === ZERO
        @test ZERO/x === ZERO
        @test x\ZERO === ZERO
        @test_throws DivideError x/ZERO
        @test_throws DivideError ZERO\x

        # Multiplication and division by -ONE which negates the other operand in a
        # multiplication.
        if !(x isa Rational{<:Unsigned})
            @test isequal((-ONE)*x, -x)
            @test isequal(x*(-ONE), -x)
            @test isequal((-ONE)\x, -x)
            @test isequal(x/(-ONE), -x)
            @test isequal((-ONE)/x, -inv(x))
            @test isequal(x\(-ONE), -inv(x))
        end

        # Addition and subtraction with ONE and -ONE.
        u = x isa Bool ? 1 :
            x isa Union{BigInt,BigFloat} ? Clong(1) : one(x)
        @test isequal(x + ONE, x + u)
        @test isequal(ONE + x, x + u)
        if !(x isa Rational{<:Unsigned})
            @test isequal(x - ONE, x - u)
            @test isequal(ONE - x, u - x)
            @test isequal(x + (-ONE), x - u)
            @test isequal((-ONE) + x, x - u)
            @test isequal(x - (-ONE), x + u)
            @test isequal((-ONE) - x, -u - x)
        end

        # Exponentiation.
        @test isequal(x^ZERO, oneunit(x))
        @test x^ONE === x
        @test isequal(x^(-ONE), inv(x))

        # div, rem, mod.
        if x isa Real
            # Division by 𝟘 throws.
            @test_throws DivideError div(x, ZERO)
            @test_throws DivideError rem(x, ZERO)
            @test_throws DivideError mod(x, ZERO)

            # Division of unsigned rationals by -𝟙 (and conversely) is not possible.
            if x isa Union{Bool,UnsignedRational}
                @test_throws InexactError div(x, -ONE)
                @test_throws InexactError rem(x, -ONE)
                @test_throws InexactError mod(x, -ONE)
                @test_throws InexactError div(-ONE, x)
                @test_throws InexactError rem(-ONE, x)
                @test_throws InexactError mod(-ONE, x)
            end

            # Test division of x by ±𝟙.
            if x isa Bool
                @test div(x, ONE) === div(x, true)
                @test rem(x, ONE) === rem(x, true)
                @test mod(x, ONE) === mod(x, true)
                if iszero(x)
                    @test_throws DivideError div(ZERO, x)
                    @test_throws DivideError rem(ZERO, x)
                    @test_throws DivideError mod(ZERO, x)
                    @test_throws DivideError div( ONE, x)
                    @test_throws DivideError rem( ONE, x)
                    @test_throws DivideError mod( ONE, x)
                else
                    @test div(ZERO, x) === div(false, x)
                    @test rem(ZERO, x) === rem(false, x)
                    @test mod(ZERO, x) === mod(false, x)
                    @test div(ONE, x) === div(true, x)
                    @test rem(ONE, x) === rem(true, x)
                    @test mod(ONE, x) === mod(true, x)
                end
            else
                S = signed_type(typeof(x))
                # Test division of x by 𝟙.
                let y = div(x, one(S))
                    if x isa Integer
                        @test y == x # test assumption
                        @test typeof(y) == typeof(x) # result of `div` has signedness of 1st operand
                        @test div(x, ONE) === x # must leave x unchanged
                    else
                        @test isequal(div(x, ONE), y)
                    end
                    @test typeof(div(x, ONE)) == typeof(y)
                end
                let y = rem(x, one(S))
                    if x isa Integer
                        @test iszero(y) # test assumption
                        @test typeof(y) == typeof(x) # result of `rem` has signedness of 1st operand
                    end
                    @test isequal(rem(x, ONE), y)
                    @test typeof(rem(x, ONE)) == typeof(y)
                end
                let y = mod(x, one(S))
                    if x isa Integer
                        @test iszero(y) # test assumption
                        @test typeof(y) == S # result of `mod` has signedness of 2nd operand
                    end
                    @test isequal(mod(x, ONE), y)
                    @test typeof(mod(x, ONE)) == typeof(y)
                end
                # Test division of x by -𝟙.
                if !(x isa UnsignedRational)
                    let y = div(x, -one(S))
                        @test isequal(div(x, -ONE), y)
                        @test typeof(div(x, -ONE)) == typeof(y)
                    end
                    let y = rem(x, -one(S))
                        @test isequal(rem(x, -ONE), y)
                        @test typeof(rem(x, -ONE)) == typeof(y)
                    end
                    let y = mod(x, -one(S))
                        @test isequal(mod(x, -ONE), y)
                        @test typeof(mod(x, -ONE)) == typeof(y)
                    end
                end
                # Test division of 𝟘, 𝟙, and -𝟙 by x.
                if iszero(x) && x isa Union{Integer,Rational}
                    @test_throws DivideError div(ZERO, x)
                    @test_throws DivideError rem(ZERO, x)
                    @test_throws DivideError mod(ZERO, x)
                    @test_throws DivideError div( ONE, x)
                    @test_throws DivideError rem( ONE, x)
                    @test_throws DivideError mod( ONE, x)
                    if !(x isa UnsignedRational)
                        @test_throws DivideError div(-ONE, x)
                        @test_throws DivideError rem(-ONE, x)
                        @test_throws DivideError mod(-ONE, x)
                    end
                else # division by x is possible
                    # Test division of 𝟘 by x.
                    let y = div(zero(S), x)
                        @test isequal(div(ZERO, x), y)
                        @test typeof(div(ZERO, x)) == typeof(y)
                    end
                    let y = rem(zero(S), x)
                        @test isequal(rem(ZERO, x), y)
                        @test typeof(rem(ZERO, x)) == typeof(y)
                    end
                    let y = mod(zero(S), x)
                        @test isequal(mod(ZERO, x), y)
                        @test typeof(mod(ZERO, x)) == typeof(y)
                    end
                    # Test division of 𝟙 by x.
                    let y = div(one(S), x)
                        @test isequal(div(ONE, x), y)
                        @test typeof(div(ONE, x)) == typeof(y)
                    end
                    let y = rem(one(S), x)
                        @test isequal(rem(ONE, x), y)
                        @test typeof(rem(ONE, x)) == typeof(y)
                    end
                    let y = mod(one(S), x)
                        @test isequal(mod(ONE, x), y)
                        @test typeof(mod(ONE, x)) == typeof(y)
                    end
                    if !(x isa UnsignedRational)
                        # Test division of -𝟙 by x.
                        let y = div(-one(S), x)
                            @test isequal(div(-ONE, x), y)
                            @test typeof(div(-ONE, x)) == typeof(y)
                        end
                        let y = rem(-one(S), x)
                            @test isequal(rem(-ONE, x), y)
                            @test typeof(rem(-ONE, x)) == typeof(y)
                        end
                        let y = mod(-one(S), x)
                            @test isequal(mod(-ONE, x), y)
                            @test typeof(mod(-ONE, x)) == typeof(y)
                        end
                    end
                end
            end
        end
    end

    @testset "Comparisons with $x" for x in others
        let z = zero(one(x)) # dimensionless zero of same type as x
            @test (x == ZERO) == (x == z)
            @test (ZERO == x) == (z == x)
            @test isequal(x, ZERO) == isequal(x, z)
            @test isequal(ZERO, x) == isequal(z, x)
            if !(x isa Complex)
                @test (x < ZERO) == (x < z)
                @test (x ≤ ZERO) == (x ≤ z)
                @test (x > ZERO) == (x > z)
                @test (x ≥ ZERO) == (x ≥ z)
                @test cmp(x, ZERO) == cmp(x, z)
                @test cmp(ZERO, x) == cmp(z, x)
            end
        end
        #
        @test (x == ONE) == (x == one(x))
        @test (ONE == x) == (one(x) == x)
        @test isequal(x, ONE) == isequal(x, one(x))
        @test isequal(ONE, x) == isequal(one(x), x)
        if !(x isa Complex)
            @test (x < ONE) == (x < one(x))
            @test (x ≤ ONE) == (x ≤ one(x))
            @test (x > ONE) == (x > one(x))
            @test (x ≥ ONE) == (x ≥ one(x))
            @test cmp(x, ONE) == cmp(x, one(x))
            @test cmp(ONE, x) == cmp(one(x), x)
        end
        #
        @test (x == -ONE) == (is_signed(x) && x == -one(x))
        @test (-ONE == x) == (is_signed(x) && -one(x) == x)
        @test isequal(x, -ONE) == (is_signed(x) && isequal(x, -one(x)))
        @test isequal(-ONE, x) == (is_signed(x) && isequal(-one(x), x))
        if !(x isa Complex)
            @test (x < -ONE) == (is_signed(x) && x < -one(x))
            @test (x ≤ -ONE) == (is_signed(x) && x ≤ -one(x))
            @test (x > -ONE) == (!is_signed(x) || x > -one(x))
            @test (x ≥ -ONE) == (!is_signed(x) || x ≥ -one(x))
            @test cmp(x, -ONE) == (is_signed(x) ? cmp(x, -one(x)) : 1)
            @test cmp(-ONE, x) == (is_signed(x) ? cmp(-one(x), x) : -1)
        end
    end

    @testset "Arithmetic with custom types" begin
        x = @inferred DimensionlessNumber(1.0)
        @test x + ZERO === x
        @test ZERO + x === x
        @test x - ZERO === x
        @test ZERO - x === -x
        # Multiplication of a non-standard number by 𝟘 must be specifically extended.
        # multiplication by 𝟙 should work.
        @test_throws MethodError ZERO*x
        @test_throws MethodError x*ZERO
        @test ONE*x === x
        @test x*ONE === x
        @test x/ONE === x
        @test ONE/x === inv(x)
        @test -ONE*x === -x
        # Operations with dimensionful number should fail here because (unlike Unitful
        # quantities) they are not specifically implemented.
        x = @inferred LengthInMeters(-2.0)
        @test_throws ArgumentError x + ZERO
        @test_throws ArgumentError x - ZERO
        @test_throws ArgumentError x - ZERO
        @test_throws ArgumentError ZERO - x

        # FIXME @test_throws ArgumentError convert(LengthInMeters{Float32}, x)
        # FIXME y = @inferred convert(DimensionlessNumber{Float32}, x)
        # FIXME @test y isa DimensionlessNumber{Float32}
        # FIXME @test y.val === Float32(x)
    end

    @testset "Bitwise operation with values of type $T and $n" for T in (
        Bool, Int8, UInt16, Int, BigInt), n in instances(Neutral)

        # Set y to be the left operand as expected by the documented logic.
        y = n == -1 ? ~zero(T) : T(n)

        x1 = (T <: Union{Bool,Unsigned} ? zero(T) : T(-15))::T
        x2 = (T <: Bool ? one(T) : T(15))::T
        x = x1:x2

        @test typeof(zero(T) | n) === T
        @test typeof(one(T) | n) === T
        @test map(Fix1(|,n), x) == map(Fix1(|,y), x)
        @test map(Fix2(|,n), x) == map(Fix2(|,y), x)

        @test typeof(zero(T) & n) === T
        @test typeof(one(T) & n) === T
        @test map(Fix1(&, n), x) == map(Fix1(&, y), x)
        @test map(Fix2(&, n), x) == map(Fix2(&, y), x)

        @test typeof(zero(T) ⊻ n) === T
        @test typeof(one(T) ⊻ n) === T
        @test map(Fix1(⊻, n), x) == map(Fix1(⊻, y), x)
        @test map(Fix2(⊻, n), x) == map(Fix2(⊻, y), x)
    end

    @testset "Bit-shifting of $x by $n" for x in filter(
        x -> x isa Integer, collect(others)), n in instances(Neutral)

        # Check value.
        @test (x << n) == (x << Int(n))
        @test (x >> n) == (x >> Int(n))
        @test (x >>> n) == (x >>> Int(n))

        # Check type.
        T = (x isa Bool && !iszero(n)) ? Int : typeof(x)
        @test typeof(x << n) === T
        @test typeof(x >> n) === T
        @test typeof(x >>> n) === T
    end

    @testset "Operation with Unitful quantities" begin
        x = 3kg
        @test Neutrals.is_dimensionless(x) == false
        @test Neutrals.is_dimensionless(x/g) == true
        @test_throws Exception x + ZERO
        @test_throws Exception x + ONE
        @test_throws Exception x + (-ONE)
        @test unit(ZERO*unit(x)) === unit(x)
        @test ZERO*unit(x) == zero(x)
        @test ZERO*unit(x) !== zero(x)
        @test unit(ONE*unit(x)) === unit(x)
        @test ONE*unit(x) == oneunit(x)
        @test ONE*unit(x) !== oneunit(x)
        @test unit(-ONE*unit(x)) === unit(x)
        @test -ONE*unit(x) == -oneunit(x)
        @test x + ZERO*unit(x) === x
        @test ZERO*unit(x) + x === x
        @test x + ONE*unit(x) === x + oneunit(x)
        @test ONE*unit(x) + x === x + oneunit(x)
        @test x - ONE*unit(x) === x - oneunit(x)
        @test ONE*unit(x) - x === oneunit(x) - x
        @test ZERO*x == zero(x)
        @test ZERO*x === ZERO*unit(x)
        @test ZERO/x == zero(inv(x))
        @test ZERO/x === ZERO/unit(x)
        @test ONE/x == inv(x)
        @test -ONE/x == -inv(x)
        @test_throws DivideError x/ZERO
        @test x/ONE === x
        @test x/-ONE == -x
    end
end

end # module
