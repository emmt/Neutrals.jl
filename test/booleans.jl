# Test specific rules involving Booleans and neutral numbers.

using Neutrals
using Neutrals: ≙
using Test
using TypeUtils



@testset "Booleans" begin

    # In Julia, Booleans are promoted to `Int` for addition, subtraction and bitwise shifts
    # (see `base/bool.jl`). The implementations of addition and subtraction of a Boolean with
    # `±𝟙` are specialized according to this.
    for x in [false, true]
        @eval begin
            # Addition.
            @test @inferred($x +  ZERO ) ===  $x
            @test @inferred($x +   ONE ) === ($x + true)::Int
            @test @inferred($x + (-ONE)) === ($x - true)::Int
            @test @inferred( ZERO  + $x) ===  $x
            @test @inferred(  ONE  + $x) === ($x + true)::Int
            @test @inferred((-ONE) + $x) === ($x - true)::Int

            # Subtraction.
            @test @inferred($x -  ZERO ) ===  $x
            @test @inferred($x -   ONE ) === ($x - true )::Int
            @test @inferred($x - (-ONE)) === ($x + true )::Int
            @test @inferred( ZERO  - $x) === (-$x       )::Int
            @test @inferred(  ONE  - $x) === ( true - $x)::Int
            @test @inferred((-ONE) - $x) === (-true - $x)::Int
        end

        # Bit shift.
        for shft in [:(<<), :(>>), :(>>>)]
            @eval begin
                @test @inferred($shft($x, ZERO)) === $shft($x,  0)::Int
                @test @inferred($shft($x,  ONE)) === $shft($x,  1)::Int
                @test @inferred($shft($x, -ONE)) === $shft($x, -1)::Int
                @test @inferred($shft(ZERO, $x)) === $shft( 0, $x)::Int
                @test @inferred($shft( ONE, $x)) === $shft( 1, $x)::Int
                @test @inferred($shft(-ONE, $x)) === $shft(-1, $x)::Int
            end
        end
    end
    #=

    # Complex{Bool} is treated specifically (see `base/complex.jl`).
    for r in [true, false], i in [true, false]
        z = Complex(r, i)

        # Check commutativity or similar properties of some operations.
        for x in instances(Neutral)
            # Commutative operations.
            for f in [:(+), :(+), :(==), :isequal]
                @eval begin
                    @test @inferred($f($x, $z)) === @inferred($f($z, $x))
                end
            end
            # x\y is equivalent to y/x.
            @eval begin
                @test @inferred($z \ $x) === @inferred($x / $z)
                if iszero($x)
                    @test_throws DivideError $x \ $z
                else
                    @test @inferred($x \ $z) === @inferred($z / $x)
                end
            end
        end

        @eval begin
            @test @inferred($z +  ZERO ) === $z
            @test @inferred($z +   ONE ) === $z + true
            @test @inferred($z + (-ONE)) === $z - true

            @test @inferred($z -  ZERO ) === $z
            @test @inferred($z -   ONE ) === $z - true
            @test @inferred($z - (-ONE)) === $z + true

            @test @inferred( ZERO  - $z) === -$z
            @test @inferred(  ONE  - $z) === true - $z
            @test @inferred((-ONE) - $z) === -true - $z

            @test @inferred( ZERO  * $z) === ZERO # FIXME
            @test @inferred(  ONE  * $z) === $z
            @test @inferred((-ONE) * $z) === -$z
            #
            @test @inferred( ZERO  / $z) === ZERO # FIXME
            @test @inferred(  ONE  / $z) === inv($z)
            @test @inferred((-ONE) / $z) === -inv($z)

            @test_throws DivideError $z / ZERO
            @test @inferred($z /   ONE ) === $z
            @test @inferred($z / (-ONE)) === -$z

            @test @inferred($z ^ ZERO ) === one($z)
            @test @inferred($z ^  ONE ) === $z
            @test @inferred($z ^(-ONE)) === inv($z)
        end
    end
    =#
end
nothing
