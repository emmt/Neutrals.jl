module NeutralsTestExt

if isdefined(Base, :get_extension)
    using Neutrals, Test
else
    using ..Neutrals, ..Test
end

using .Neutrals: maybe_neutral, ≙, strict_isequal, ≗, sloppy_isequal, signed_type
import .Neutrals: test_binary_operations
using TypeUtils

function test_binary_operations(vals::Number...; kwds...)
    for x in vals
        test_binary_operations(x; kwds...)
    end
end

function test_binary_operations(vals::Union{Tuple{Number,Vararg{Number}},
                                            AbstractArray{<:Number}}; kwds...)
    for x in vals
        test_binary_operations(x; kwds...)
    end
end

test_info(op::AbstractString, x::Number) = test_info(stderr, op, x)
test_info(io::IO, op::AbstractString, x::Number) =
    println(io, "Test ", op, " with `x = $(typeof(x))($x)`")

function test_binary_operations(x::Number; debug::Bool=false)
    # Type and signed type of `x`.
    T = typeof(x)
    S = signed_type(typeof(x))

    # Operator to test for equality as strictly as possible for a computed result.
    eq = x isa Union{BigInt, BigFloat} ? :(≙) : :(===)

    # Test arithmetic binary operations.
    debug && test_info("arithmetic binary operations (`+`, `-`, `*`, `/`, and `^`)", x)
    xp = x isa Bool ? Int(x) : x # for the addition and subtraction
    @eval begin
        @test ===(@inferred($x +  ZERO ), $xp)
        @test $eq(@inferred($x +   ONE ), $xp + one($xp))
        @test $eq(@inferred($x + (-ONE)), $xp - one($xp))

        @test ===(@inferred($x -  ZERO ), $xp)
        @test $eq(@inferred($x -   ONE ), $xp - one($xp))
        @test $eq(@inferred($x - (-ONE)), $xp + one($xp))

        @test $eq(@inferred( ZERO  - $x), -$xp)
        @test $eq(@inferred(  ONE  - $x), one($xp) - $xp)
        @test $eq(@inferred((-ONE) - $x), -one($xp) - $xp)

        @test $eq(@inferred( ZERO  * $x), zero($x))
        @test ===(@inferred(  ONE  * $x), $x)
        @test $eq(@inferred((-ONE) * $x), -$x)
        #
        @test $eq(@inferred( ZERO  / $x), float(zero($x))) # FIXME units
        @test $eq(@inferred(  ONE  / $x), inv($x))
        @test $eq(@inferred((-ONE) / $x), -inv($x))

        @test @inferred($x / ZERO) isa float(typeof($x))
        @test isinf(@inferred($x / ZERO))
        @test signbit(@inferred($x / ZERO)) == signbit($x)
        @test $eq(@inferred($x / ONE), $x)
        @test $eq(@inferred($x / (-ONE)), -$x)

        @test $eq(@inferred($x ^ ZERO ), one($x))
        @test $eq(@inferred($x ^  ONE ), $x)
        @test $eq(@inferred($x ^(-ONE)), inv($x))
    end

    # Check commutativity of some arithmetic operations.
    for f in [:(+), :(*)], y in instances(Neutral)
        @eval begin
            @test $eq(@inferred($f($x, $y)), @inferred($f($y, $x)))
        end
    end

    # Check that `x\y` is equivalent to `y/x`.
    for y in instances(Neutral)
        @eval begin
            @test $eq(@inferred($x \ $y), @inferred($y / $x))
            if iszero($y) && $x === ZERO
                @test_throws DivideError $y \ $x
            else
                @test $eq(@inferred($y \ $x), @inferred($x / $y))
            end
        end
    end

    # Test commutative comparisons.
    debug && test_info("commutative comparisons (`==`, `isqual`, and `!=`)", x)
    for f in [:(==), :isequal, :(!=)]
        # Check result of comparisons.
        @eval begin
            @test @inferred($f($x, ZERO)) === $f($x,  0)
            @test @inferred($f($x,  ONE)) === $f($x,  1)
            @test @inferred($f($x, -ONE)) === $f($x, -1)
        end
        # Check commutativity.
        for y in instances(Neutral)
            @eval begin
                @test @inferred($f($x, $y)) === @inferred($f($y, $x))
            end
        end
    end

    # Test non-commutative comparisons. TODO Test for NaNs.
    if !(bare_type(x) <: Complex) && !isnan(x)
        debug && test_info(
            "non-commutative comparisons (`<`, `<=`, `isless`, `cmp`, `>`, and `!>=`)", x)
        for y in instances(Neutral)
            # Check result of comparisons.
            for f in [:(<), :(<=), :isless, #= :cmp, =# :(>), :(>=)]
                @eval begin
                    @test @inferred($f($x, $y)) === $f($x, Int($y))
                    @test @inferred($f($y, $x)) === $f(Int($y), $x)
                end
            end
            # `cmp` is anti-commutative.
            let f = :cmp
                # FIXME Use `==`, not `===` for `cmp` because it yields `Int32` (not `Int`)
                #       for `BigFloat`.
                @eval begin
                    @test @inferred($f($x, $y)) == -@inferred($f($y, $x))
                    @test @inferred($f($x, $y)) == $f($x, Int($y))
                    @test @inferred($f($y, $x)) == $f(Int($y), $x)
                end
            end
            # Test that `(x < y) === (y > x)` and that `(x ≤ y) === (y ≥ x)`.
            for (f, g) in [:(<) => :(>), :(<=) => :(>=)]
                @eval begin
                    @test @inferred($f($x, $y)) === @inferred($g($y, $x))
                    @test @inferred($f($y, $x)) === @inferred($g($x, $y))
                end
            end
        end
    end

    # Test bitwise binary operations.
    if bare_type(x) <: Integer
        debug && test_info("bitwise binary operations (`|`, `&`, and `xor`)", x)
        # Check result of bitwise operations. Type shall be preserved.
         @eval begin
            @test ===(@inferred($x |  ZERO )::$T, $x)
            @test $eq(@inferred($x |   ONE )::$T, $x |   one($x))
            @test $eq(@inferred($x | (-ONE))::$T, $x | ~zero($x))
            #
            @test $eq(@inferred($x &  ZERO )::$T, $x &  zero($x))
            @test $eq(@inferred($x &   ONE )::$T, $x &   one($x))
            @test $eq(@inferred($x & (-ONE))::$T, $x & ~zero($x))
            #
            @test $eq(@inferred(xor($x,  ZERO ))::$T, xor($x,  zero($x)))
            @test $eq(@inferred(xor($x,   ONE ))::$T, xor($x,   one($x)))
            @test $eq(@inferred(xor($x, (-ONE)))::$T, xor($x, ~zero($x)))
        end
        # Check commutativity of bitwise operations.
        for f in [:(|), :(&), :xor], y in instances(Neutral)
            @eval begin
                @test $eq(@inferred($f($x, $y)), @inferred($f($y, $x)))
            end
        end
    end

    # Test bit-shifting operations.
    if bare_type(x) <: Integer
        debug && test_info("bit-shifting operations (`<<`, `>>`, and `>>>`)", x)
        for shft in [:(<<), :(>>), :(>>>)], y in instances(Neutral)
            @eval begin
                # Use `Int8` as the smallest integer type able to represent exactly a
                # neutral value.
                @test @inferred($shft($x, $y)) === $shft($x, Int8($y))
                @test @inferred($shft($y, $x)) === $shft(Int($y), $x)::Int
            end
        end
    end

    # Test Euclidean division.
    if !(bare_type(x) <: Complex)
        debug && test_info("Euclidean division (`div`, `rem`, and `mod`)", x)
        for f in [:(div), :(rem), :(mod)], y in instances(Neutral)
            @eval begin
                if iszero($y)
                    # `div(x,𝟘)`, `rem(x,𝟘)`, and `mod(x,𝟘)` throw `DivideError`. FIXME This
                    # rule is ok for integers and rationals but may be not for floating-point.
                    @test_throws DivideError $f($x, $y)
                else
                    @test $eq(@inferred($f($x, $y)), $f($x, Int8($y)))
                end
            end
        end
    end
end

end # module
