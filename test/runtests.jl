using Neutrals
using Test
using TypeUtils

@testset "Neutrals.jl" begin
    maybe(::Type{Neutral}, x::Integer) =  (-1 ≤ x ≤ 1 ? Neutral(x) : x)
    types = (Integer,
             Bool,
             Int8, Int16, Int32, Int64, Int128, BigInt,
             UInt8, UInt16, UInt32, UInt64, UInt128,
             AbstractFloat,
             Float16, Float32, Float64, BigFloat,
             Rational{Int8}, Rational{UInt8},
             Complex{Bool}, Complex{Int16}, Complex{Float32})
    #integers = filter(T -> T <: Integer, collect(types))
    #floats = filter(T -> T <: AbstractFloat, collect(types))
    others = (true, false,
              0x0, 0x1,
              0, 1, -1, 2,
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

    @testset "Constructors of $v" for (k, v) in (0 => ZERO, 1 => ONE, -1 => -ONE)
        # Consistency.
        @test v ∈ instances(Neutral)
        @test Int(v) === k
        @test Neutrals.value(v) === k

        # Constructors.
        @test Neutral{k}() === v
        @test Neutral(k) === v
        @test Neutral(v) === v
        @test Neutral{k}(v) === v
        @test Neutral(Int8(k)) === v
        @test Neutral{k}(Int8(k)) === v
        @test Neutral(float(k)) === v
        @test Neutral{k}(float(k)) === v
        @test_throws Exception Neutral{Int8(k)}()
    end

    @testset "Unary functions of $x" for x in instances(Neutral)
        @test summary(x) isa String
        @test repr(x) isa String
        @test +x === x
        @test -x === Neutral(-Int(x))
        @test ~x === (-1 ≤ ~Int(x) ≤ 1 ? Neutral(~Int(x)) : ~Int(x))
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
        if iszero(Int(x))
            @test_throws DivideError inv(x)
        else
            @test inv(x) === x
        end
        @test iseven(x) === iseven(Int(x))
        @test isodd(x) === isodd(Int(x))
    end

    @testset "Conversion of $x to type $T" for T in types, x in instances(Neutral)
        if T === Bool # to do these test once
            @test convert(typeof(x), x) === x
            @test convert(Neutral, x) === x
            @test typeof(x)(x) === x
            @test convert(Integer, x) === x
            @test Integer(x) === x
        end
        if is_signed(T) || Int(x) ≥ 0
            y = @inferred convert(T, x)
            z = @inferred T(x)
            @test y isa T
            @test z isa T
            @test y == T(Int(x))
            @test z == T(Int(x))
            if T === AbstractFloat
                @test y isa Float64
                @test z isa Float64
                @test float(x) === y
                @test float(x) === z
            end
        else
            @test_throws InexactError convert(T, x)
            @test_throws InexactError T(x)
        end
        if T <: Integer
            y = @inferred rem(x, T) # x % T
            @test y isa T
            if isconcretetype(T)
                @test y == (Int(x) % T)
            else
                @test y === x
            end
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
        if Int(y) == 0
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
        # ZERO as neutral element of addition.
        @test ZERO + x === x
        @test x + ZERO === x
        @test isequal(ZERO - x, -x)
        @test x - ZERO === x

        u = x isa Bool ? 1 :
            x isa Union{BigInt,BigFloat} ? Clong(1) : one(x)
        @test isequal(x + ONE, x + u)
        @test isequal(ONE + x, x + u)
        @test isequal(x - ONE, x - u)
        @test isequal(ONE - x, u - x)
        if is_signed(x) || x isa Bool
            @test isequal(x + (-ONE), x - u)
            @test isequal((-ONE) + x, x - u)
            @test isequal(x - (-ONE), x + u)
            @test isequal((-ONE) - x, -u - x)
        else
            @test_throws InexactError x + (-ONE)
            @test_throws InexactError (-ONE) + x
            @test_throws InexactError x - (-ONE)
            @test_throws InexactError (-ONE) - x
        end

        # ONE as neutral element of multiplication.
        @test ONE*x === x
        @test x*ONE === x
        @test ONE\x === x
        @test x/ONE === x

        # Multiplication by ZERO yields ZERO.
        @test ZERO*x === ZERO
        @test x*ZERO === ZERO

        # Division by ZERO.
        @test_throws DivideError x/ZERO
        @test_throws DivideError ZERO\x

        # Multiplication and division by -ONE negate other operand.
        @test isequal((-ONE)*x, -x)
        @test isequal(x*(-ONE), -x)
        @test isequal((-ONE)\x, -x)
        @test isequal(x/(-ONE), -x)
    end

end
