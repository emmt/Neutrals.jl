# Test specific rules involving Booleans and neutral numbers.

using Neutrals
using Neutrals: ≙
using Test
using TypeUtils

@testset "Booleans" begin

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
end
nothing
