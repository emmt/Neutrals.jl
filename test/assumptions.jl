# Check assumptions made about how Julia treats ordinary numbers.

isdefined(@__MODULE__, :(≙)) || include("setup.jl")

@testset "Assumptions" begin
    for T in [Bool, UInt8, UInt16, UInt32, UInt64, UInt128,
              UInt8, Int16, Int32, Int64, Int128, BigInt,
              Float16, Float32, BigFloat]
        # Operator for testing equivalence of values.
        eq = T <: Union{BigInt, BigFloat} ? :(≙) : :(===)

        # 0 and 1 are exactly representable by any numeric type.
        @eval begin
            @test $eq($T(0), zero($T))
            @test $eq($T(1), one($T))
        end
        if T <: Integer
            @eval begin
                @test $eq($T(0), (0 % $T))
                @test $eq($T(1), (1 % $T))
            end
        end

        # For Booleans and unsigned integers, -1 is not representable. It is exactly
        # representable by any other numeric types.
        if T <: Union{Bool, Unsigned}
            @eval @test_throws InexactError $T(-1)
        else
            @eval @test @inferred($T(-1)) < zero($T)
            @eval @test @inferred($T(-1)) == -1
        end

        # Test unary `-` and `~` on 0 and 1 for integers.
        if T <: Bool
            # Booleans are special.
            @test ((-1) % Bool) === ~zero(Bool) === true
            @test @inferred(-true) === -1
            @test @inferred(-false) === 0
            @test @inferred(~true) === false
            @test @inferred(~false) === true
        elseif T <: Integer
            # For integer type `T`, `((-1) % T)`, `-one(T)`, and `~zero(T)` are the same thing.
            @eval begin
                # ((-1) % T) == -T(1)
                @test $eq(((-1) % $T), -$T(1))
                @test $eq(((-1) % $T), ~$T(0))
            end
        end

        # Exhaustive tests on all values of small integer types.
        if T <: Union{Bool, Int8, UInt8}
            # Optimization for rem(x, 𝟙) and mod(x, 𝟙) when x is an integer.
            @eval begin
                @test all(iszero, (rem(x, one(x)) for x in typemin($T):typemax($T)))
                @test all(iszero, (mod(x, one(x)) for x in typemin($T):typemax($T)))
            end
        end
    end

    # Optimization for rem(x, -𝟙) and mod(x, -𝟙) when x is a signed integer.
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
nothing
