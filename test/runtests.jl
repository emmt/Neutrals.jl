module TestingNeutrals

using Neutrals
using Test
using TypeUtils
using Unitful, Unitful.DefaultSymbols

using Base: Fix1, Fix2

struct LengthInMeters{T<:Real} <: Number
    len::T
end

Neutrals.is_dimensionless(::Type{<:LengthInMeters}) = false
Base.zero(::Type{LengthInMeters{T}}) where {T} = LengthInMeters(zero(T))
Base.one(::Type{LengthInMeters{T}}) where {T} = one(T)
Base.oneunit(::Type{LengthInMeters{T}}) where {T} = LengthInMeters(oneunit(T))
Base.:-(x::LengthInMeters) = DimensionlessNumber(-x.val)

struct DimensionlessNumber{T<:Real} <: Number
    val::T
end

Neutrals.is_dimensionless(::Type{<:DimensionlessNumber}) = true
Neutrals.impl_conv(::Type{DimensionlessNumber{T}}, x::Neutral) where {T} =
    DimensionlessNumber{T}(x)
Base.zero(::Type{DimensionlessNumber{T}}) where {T} = DimensionlessNumber(zero(T))
Base.one(::Type{DimensionlessNumber{T}}) where {T} = DimensionlessNumber(one(T))
Base.oneunit(::Type{DimensionlessNumber{T}}) where {T} = DimensionlessNumber(oneunit(T))
Base.:-(x::DimensionlessNumber) = DimensionlessNumber(-x.val)
Base.:inv(x::DimensionlessNumber) = DimensionlessNumber(inv(x.val))

@testset "Neutrals.jl" begin
    maybe(::Type{Neutral}, x::Integer) = (-1 ≤ x ≤ 1 ? Neutral(x) : x)
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
              BigInt(0), BigInt(1), BigInt(-1), BigInt(3),
              BigFloat(0), BigFloat(1), BigFloat(-1), BigFloat(3))
    numbers = (instances(Neutral)..., others...)

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
        @test_throws ArgumentError convert(LengthInMeters{Float32}, x)
        y = @inferred convert(DimensionlessNumber{Float32}, x)
        @test y isa DimensionlessNumber{Float32}
        @test y.val === Float32(x)
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

    @testset "Binary operations with $x" for x in others
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

        # Comparisons.
        let z = zero(one(x)) # dimensionless zero of same type as x
            @test (x == ZERO) == (x == z)
            @test (ZERO == x) == (z == x)
            @test isequal(x, ZERO) == isequal(x, z)
            @test isequal(ZERO, x) == isequal(z, x)
            @test (x < ZERO) == (x < z)
            @test (x ≤ ZERO) == (x ≤ z)
            @test (x > ZERO) == (x > z)
            @test (x ≥ ZERO) == (x ≥ z)
            @test cmp(x, ZERO) == cmp(x, z)
            @test cmp(ZERO, x) == cmp(z, x)
        end
        #
        @test (x == ONE) == (x == one(x))
        @test (ONE == x) == (one(x) == x)
        @test isequal(x, ONE) == isequal(x, one(x))
        @test isequal(ONE, x) == isequal(one(x), x)
        @test (x < ONE) == (x < one(x))
        @test (x ≤ ONE) == (x ≤ one(x))
        @test (x > ONE) == (x > one(x))
        @test (x ≥ ONE) == (x ≥ one(x))
        @test cmp(x, ONE) == cmp(x, one(x))
        @test cmp(ONE, x) == cmp(one(x), x)
        #
        @test (x == -ONE) == (is_signed(x) && x == -one(x))
        @test (-ONE == x) == (is_signed(x) && -one(x) == x)
        @test isequal(x, -ONE) == (is_signed(x) && isequal(x, -one(x)))
        @test isequal(-ONE, x) == (is_signed(x) && isequal(-one(x), x))
        @test (x < -ONE) == (is_signed(x) && x < -one(x))
        @test (x ≤ -ONE) == (is_signed(x) && x ≤ -one(x))
        @test (x > -ONE) == (!is_signed(x) || x > -one(x))
        @test (x ≥ -ONE) == (!is_signed(x) || x ≥ -one(x))
        @test cmp(x, -ONE) == (is_signed(x) ? cmp(x, -one(x)) : 1)
        @test cmp(-ONE, x) == (is_signed(x) ? cmp(-one(x), x) : -1)
    end

    @testset "Arithmetic with custom types" begin
        x = @inferred DimensionlessNumber(1.0)
        @test x + 𝟘 === x
        @test 𝟘 + x === x
        @test x - 𝟘 === x
        @test 𝟘 - x === -x
        # Multiplication of a non-standard number by 𝟘 must be specifically extended.
        # multiplication by 𝟙 should work.
        @test_throws MethodError 𝟘*x
        @test_throws MethodError x*𝟘
        @test 𝟙*x === x
        @test x*𝟙 === x
        @test x/𝟙 === x
        @test 𝟙/x === inv(x)
        @test -𝟙*x === -x
        # Operations with dimensionful number should fail here because (unlike Unitful
        # quantities) they are not specifically implemented.
        x = @inferred LengthInMeters(-2.0)
        @test_throws ArgumentError x + 𝟘
        @test_throws ArgumentError x - 𝟘
        @test_throws ArgumentError x - 𝟘
        @test_throws ArgumentError 𝟘 - x
    end

    @testset "Bitwise operation with values of type $T and $n" for T in (
        Bool, Int8, UInt16, Int, BigInt), n in instances(Neutral)

        # Set y to be the left operand as expected by the documented logic.
        y = n == -1 ? (T <: Bool ? true : -one(T)) : T(n)

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
        @test_throws Exception x + 𝟘
        @test_throws Exception x + 𝟙
        @test_throws Exception x + (-𝟙)
        @test unit(𝟘*unit(x)) === unit(x)
        @test 𝟘*unit(x) == zero(x)
        @test 𝟘*unit(x) !== zero(x)
        @test unit(𝟙*unit(x)) === unit(x)
        @test 𝟙*unit(x) == oneunit(x)
        @test 𝟙*unit(x) !== oneunit(x)
        @test unit(-𝟙*unit(x)) === unit(x)
        @test -𝟙*unit(x) == -oneunit(x)
        @test x + 𝟘*unit(x) === x
        @test 𝟘*unit(x) + x === x
        @test x + 𝟙*unit(x) === x + oneunit(x)
        @test 𝟙*unit(x) + x === x + oneunit(x)
        @test x - 𝟙*unit(x) === x - oneunit(x)
        @test 𝟙*unit(x) - x === oneunit(x) - x
        @test 𝟘/x == zero(inv(x))
        @test 𝟙/x == inv(x)
        @test -𝟙/x == -inv(x)
        @test_throws DivideError x/𝟘
        @test x/𝟙 == x
        @test x/-𝟙 == -x
    end
end

end # module
