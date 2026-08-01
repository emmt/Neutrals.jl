# Test binary operations on neutral numbers.

using Neutrals
using Neutrals: ≙, ≗, sloppy_isequal, strict_isequal, maybe_neutral, signed_type
using Test
using TypeUtils

@testset "Binary" begin
    # NOTE Many tests are wrapped in an `@eval` block so that the values of the arguments
    #      are explicitly shown in error messages.

    # Binary operations between neutral numbers.
    for x in instances(Neutral), y in instances(Neutral)
        vx, vy = Int(x), Int(y)
        @eval begin
            # Arithmetic.
            @test @inferred($x + $y) === maybe_neutral($vx + $vy)
            @test @inferred($x - $y) === maybe_neutral($vx - $vy)
            @test @inferred($x * $y) === Neutral($vx * $vy)
            if $vy == 0
                @test_throws DivideError $x / $y
                @test_throws DivideError div($x, $y)
                @test_throws DivideError rem($x, $y)
                @test_throws DivideError mod($x, $y)
            else
                @test @inferred($x / $y) === Neutral($vx / $vy)
                @test @inferred(div($x, $y)) === Neutral(div($vx, $vy))
                @test @inferred(rem($x, $y)) === Neutral(rem($vx, $vy))
                @test @inferred(mod($x, $y)) === Neutral(mod($vx, $vy))
            end

            # Power. (FIXME: implemented behavior is weird.)
            @test @inferred($x ^ $y) === Neutral($vy == 0 ? 1 : $vx)

            # Bitwise binary operations.
            @test @inferred($x | $y) === Neutral($vx | $vy)
            @test @inferred($x & $y) === Neutral($vx & $vy)
            @test @inferred(xor($x, $y)) === maybe_neutral(xor($vx, $vy))
            @test @inferred($x << $y) === maybe_neutral($vx << $vy)
            @test @inferred($x >> $y) === maybe_neutral($vx >> $vy)
            @test @inferred($x >>> $y) === maybe_neutral($vx >>> $vy)

            # Comparisons.
            @test @inferred($x == $y) === ($vx == $vy)
            @test @inferred($x != $y) === ($vx != $vy)
            @test @inferred($x === $y) === ($vx === $vy)
            @test @inferred($x !== $y) === ($vx !== $vy)
            @test @inferred($x < $y) === ($vx < $vy)
            @test @inferred($x <= $y) === ($vx <= $vy)
            @test @inferred($x > $y) === ($vx > $vy)
            @test @inferred($x >= $y) === ($vx >= $vy)
            @test @inferred(isequal($x, $y)) === isequal($vx, $vy)
            @test @inferred(isless($x, $y)) === isless($vx, $vy)
            @test @inferred(cmp($x, $y)) === cmp($vx, $vy)

            @test @inferred(flipsign($x, $y)) === Neutral(flipsign($vx, $vy))
            @test @inferred(copysign($x, $y)) === Neutral(copysign($vx, $vy))

            # Promote rules.
            @test @inferred(promote($x, $y)) === ($vx == $vy ? ($x, $y) : ($vx, $vy))
        end
    end

    # FIXME Use array of numbers, not tuple.
    for x in (true, false,
              0x0, 0x1, 0x5,
              0, 1, -1, 2, 7, -6,
              0x00//0x01, 0x01//0x01, 0x01//0x03,
              0//1, 1//1, -1//1, -1//2,
              0.0f0, 1.0f0, -1.0f0, 2.0f0, Inf32, -Inf32, NaN32,
              0.0, 1.0, -1.0, 0.4, Inf, -Inf, NaN, -NaN,
              π,
              0 + 0im, 1.0 - 2.0im, complex(-1//1, 3//1),
              complex(false,false), complex(true,false), complex(false,true), complex(true,true),
              #= complex(pi, pi), FIXME =#
              BigInt(0), BigInt(1), BigInt(-1), BigInt(3),
              BigFloat(0), BigFloat(1), BigFloat(-1), BigFloat(3))
        # Type and signed type of `x`.
        T = typeof(x)
        S = signed_type(typeof(x))

        # Operator for testing equivalence of values.
        eq = isa(x, Union{BigInt, BigFloat}) ? :(≙) : :(===)

        # One of a suitable type to yield a result of the correct type in some binary
        # operations with a neutral number.
        u = x isa Bool ? 1 : x isa Union{BigInt,BigFloat} ? Clong(1) : one(x)

        @eval begin
            # Addition and subtraction with ZERO, the neutral element for the addition of
            # numbers.
            @test @inferred(ZERO + $x) === $x
            @test @inferred($x + ZERO) === $x
            @test @inferred($x - ZERO) === $x
            if !($x isa Rational{<:Unsigned})
                @test $eq(@inferred(ZERO - $x), -$x)
            end

            # Addition and subtraction with ONE and -ONE.
            @test $eq(@inferred($x + ONE), $x + $u)
            @test $eq(@inferred(ONE + $x), $x + $u)
            if !($x isa Rational{<:Unsigned})
                @test $eq(@inferred($x - ONE), $x - $u)
                @test $eq(@inferred(ONE - $x), $u - $x)
                @test $eq(@inferred($x + (-ONE)), $x - $u)
                @test $eq(@inferred((-ONE) + $x), $x - $u)
                @test $eq(@inferred($x - (-ONE)), $x + $u)
                @test $eq(@inferred((-ONE) - $x), -$u - $x)
            end

            # Multiplication and division by ONE, the neutral element for the multiplication
            # of numbers.
            @test @inferred(ONE * $x) === $x
            @test @inferred($x * ONE) === $x
            @test @inferred(ONE \ $x) === $x
            @test @inferred($x / ONE) === $x
            @test $eq(@inferred(ONE / $x), inv($x))
            @test $eq(@inferred($x \ ONE), inv($x))

            # Multiplication and division by ZERO, a strong zero for the multiplication of
            # numbers.
            @test @inferred(ZERO * $x) === ZERO
            @test @inferred($x * ZERO) === ZERO
            @test @inferred(ZERO / $x) === ZERO
            @test @inferred($x \ ZERO) === ZERO
            @test_throws DivideError $x / ZERO
            @test_throws DivideError ZERO \ $x

            # Multiplication and division by -ONE which negates the other operand in a
            # multiplication.
            if !($x isa Rational{<:Unsigned})
                @test $eq(@inferred((-ONE) * $x), -$x)
                @test $eq(@inferred($x * (-ONE)), -$x)
                @test $eq(@inferred((-ONE) \ $x), -$x)
                @test $eq(@inferred($x / (-ONE)), -$x)
                if ($x isa AbstractFloat) && !($x isa BigFloat) && isnan($x)
                    # FIXME see comment about sloppy_isequal
                    @test sloppy_isequal(@inferred((-ONE) / $x), -inv($x))
                    @test sloppy_isequal(@inferred($x \ (-ONE)), -inv($x))
                else
                    @test $eq(@inferred((-ONE) / $x), -inv($x))
                    @test $eq(@inferred($x \ (-ONE)), -inv($x))
                end
            end

            # Exponentiation.
            if !($x isa AbstractIrrational) # FIXME, solution can be x^ZERO -> ONE
                @test $eq(@inferred($x ^ ZERO), oneunit($x))
            end
            @test @inferred($x ^ ONE) === $x
            @test $eq(@inferred($x^(-ONE)), inv($x))

            # Truncated division, remainder, etc.
            if $x isa Real
                # `div(x,𝟘)`, `rem(x,𝟘)`, and `mod(x,𝟘)` throw `DivideError`. FIXME This
                # rule is ok for integers and rationals but may be not for floating-point.
                @test_throws DivideError div($x, ZERO)
                @test_throws DivideError rem($x, ZERO)
                @test_throws DivideError mod($x, ZERO)

                # Truncated division of a neutral number by non-neutral `x`.
                if $x isa Union{Integer, Rational} && iszero($x)
                    # Integer division by `x` is not possible.
                    @test_throws DivideError div(ZERO, $x)
                    @test_throws DivideError rem(ZERO, $x)
                    @test_throws DivideError mod(ZERO, $x)
                    #
                    @test_throws DivideError div( ONE, $x)
                    @test_throws DivideError rem( ONE, $x)
                    @test_throws DivideError mod( ONE, $x)
                    #
                    if !($x isa Union{Bool, Rational{<:Union{Bool, Unsigned}}})
                        @test_throws DivideError div(-ONE, $x)
                        @test_throws DivideError rem(-ONE, $x)
                        @test_throws DivideError mod(-ONE, $x)
                    end
                else
                    # Truncated division by `x` is possible.
                    @test @inferred(div(ZERO, $x)) ≙ div(zero($S), $x) # FIXME should be T or x
                    @test @inferred(rem(ZERO, $x)) ≙ rem(zero($S), $x) # FIXME idem
                    @test @inferred(mod(ZERO, $x)) ≙ mod(zero($S), $x) # FIXME idem
                    #
                    @test @inferred(div(ONE, $x)) ≙ div(one($S), $x) # FIXME should be T or x
                    @test @inferred(rem(ONE, $x)) ≙ rem(one($S), $x) # FIXME idem
                    @test @inferred(mod(ONE, $x)) ≙ mod(one($S), $x) # FIXME idem
                    #
                    if !($x isa Union{Bool, Rational{<:Union{Bool, Unsigned}}})
                        @test @inferred(div(-ONE, $x)) ≙ div(-one($S), $x)
                        @test @inferred(rem(-ONE, $x)) ≙ rem(-one($S), $x)
                        @test @inferred(mod(-ONE, $x)) ≙ mod(-one($S), $x)
                    end
                end

                # Truncated division of Booleans and unsigned rationals by -𝟙 (and
                # conversely) is not possible. FIXME Same rule for unsigned integers?
                if $x isa Union{Bool, Rational{<:Union{Bool, Unsigned}}}
                    @test_throws InexactError div($x, -ONE)
                    @test_throws InexactError rem($x, -ONE)
                    @test_throws InexactError mod($x, -ONE)
                    @test_throws InexactError div(-ONE, $x)
                    @test_throws InexactError rem(-ONE, $x)
                    @test_throws InexactError mod(-ONE, $x)
                end
            end
        end
    end
end
nothing
