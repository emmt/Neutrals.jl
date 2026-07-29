# Test unitful numbers.

using Neutrals
using TypeUtils
using Unitful, Unitful.DefaultSymbols

isdefined(@__MODULE__, :(≙)) || include("setup.jl")

@testset "Unitful quantities" begin
    for x in [3kg, -2.5cm/s]
        # Dimensionful quantities are not allowed in addition or subtraction with a
        # neutral number.
        for y in instances(Neutral)
            @eval begin
                @test_throws Exception $x + $y
                @test_throws Exception $y + $x
                @test_throws Exception $x - $y
                @test_throws Exception $y - $x
            end
        end

        # Addition is commutative and preserve units.
        for y in instances(Neutral)
            @eval begin
                @test @inferred($x + $y*unit($x)) === @inferred($y*unit($x) + $x)
                @test @inferred(unit($x + $y*unit($x))) === unit($x)
            end
        end

        # Additive identities.
        @eval begin
            @test @inferred($x +   ZERO*unit($x)) === $x
            @test @inferred($x +    ONE*unit($x)) === $x + oneunit($x)
            @test @inferred($x + (-ONE)*unit($x)) === $x - oneunit($x)
        end

        # Subtraction is anti-commutative and preserve units.
        for y in instances(Neutral)
            @eval begin
                @test @inferred($x - $y*unit($x)) === @inferred(-($y*unit($x) - $x))
                @test @inferred($y*unit($x) - $x) === @inferred(-($x - $y*unit($x)))
                @test @inferred(unit($x - $y*unit($x))) === unit($x)
                @test @inferred(unit($y*unit($x) - $x)) === unit($x)
            end
        end

        # Identities for the subtraction.
        @eval begin
            @test @inferred($x -   ZERO*unit($x)) === $x
            @test @inferred($x -    ONE*unit($x)) === $x - oneunit($x)
            @test @inferred($x - (-ONE)*unit($x)) === $x + oneunit($x)
            @test @inferred(  ZERO*unit($x) - $x) === -$x
            @test @inferred(   ONE*unit($x) - $x) ===  oneunit($x) - $x
            @test @inferred((-ONE)*unit($x) - $x) === -oneunit($x) - $x
        end

        # Multiplication is commutative.
        for y in instances(Neutral)
            @eval begin
                @test @inferred($x * $y) === @inferred($y * $x)
            end
        end

        # Multiplicative identities.
        @eval begin
            @test @inferred( ZERO  * $x) ==  zero($x) # FIXME shall be === in next release
            @test @inferred(  ONE  * $x) ===      $x
            @test @inferred((-ONE) * $x) ===     -$x
        end

        # Multiplication of units.
        for y in instances(Neutral)
            @eval begin
                # Static numbers.
                @test is_static_number(@inferred($y*unit($x))) == true
                @test is_static_number(typeof(@inferred($y*unit($x)))) == true

                # Transfer of units by multiplication.
                @test unit(@inferred($y*unit($x))) === unit($x)
                @test unit(@inferred(unit($x)*$y)) === unit($x)
            end
        end

        # Division.
        @eval begin
            @test @inferred( ZERO  / $x) == zero(inv($x)) # FIXME shall be === in next release
            @test @inferred(  ONE  / $x) === inv($x)
            @test @inferred((-ONE) / $x) === -inv($x)
            @test_throws DivideError $x / ZERO
            @test @inferred($x /  ONE) ===  $x
            @test @inferred($x / -ONE) === -$x
        end
    end

    # Arrays with units.
    x = [-1.0, 2.0]
    y = x.*kg

    z = @inferred ZERO*y
    @test @inferred(y*ZERO) ≙ z
    @test sizeof(z) == 0
    @test length(z) == length(y)
    @test size(z) == size(y)
    @test axes(z) == axes(y)
    @test eltype(z) === typeof(ZERO*kg)

    @test @inferred(ONE*y) === y
    @test @inferred(y*ONE) === y

    @test (-ONE)*y ≙ -y
    @test y*(-ONE) ≙ -y

    @test_throws DivideError y/ZERO
    @test_throws DivideError ZERO\y

    @test @inferred(ONE\y) === y
    @test @inferred(y/ONE) === y

    @test (-ONE)\y ≙ -y
    @test y/(-ONE) ≙ -y

    # Elementwise.
    x = @inferred Array{typeof(ZERO*cm)}(undef, 2, 3, 4)
    @test_throws DivideError  ZERO  ./ x
    @test_throws DivideError   ONE  ./ x
    @test_throws DivideError (-ONE) ./ x
    @test_throws DivideError x .\  ZERO
    @test_throws DivideError x .\   ONE
    @test_throws DivideError x .\ (-ONE)
    let r = @inferred   ZERO .* x
        @test @inferred(ZERO  * x) ≙ r
        @test @inferred(x .* ZERO) ≙ r
        @test @inferred(x  * ZERO) ≙ r
    end
    let r = @inferred   ONE .* x
        @test @inferred(ONE  * x) ≙ r
        @test @inferred(x .* ONE) ≙ r
        @test @inferred(x  * ONE) ≙ r
    end
    let r = @inferred   (-ONE) .* x
        @test @inferred((-ONE)  * x) ≙ r
        @test @inferred(x .* (-ONE)) ≙ r
        @test @inferred(x  * (-ONE)) ≙ r
    end

    x = @inferred Array{typeof(ONE*cm)}(undef, 2, 3, 2)
    @test  ZERO  .* x ≙ ZERO*x
    @test  ZERO   * x ≙ ZERO*x
    @test   ONE  .* x === x
    @test   ONE   * x === x
    @test (-ONE) .* x ≙ -x
    @test (-ONE)  * x ≙ -x
    @test x .*  ZERO  ≙ ZERO*x
    @test x  *  ZERO  ≙ ZERO*x
    @test x .*   ONE  === x
    @test x  *   ONE  === x
    @test x .* (-ONE) ≙ -x
    @test x  * (-ONE) ≙ -x

    @test_throws DivideError x ./ ZERO
    @test_throws DivideError x  / ZERO
    @test x ./   ONE  === x
    @test x  /   ONE  === x
    @test x ./ (-ONE) ≙ -x
    @test x  / (-ONE) ≙ -x
    @test_throws DivideError ZERO .\ x
    @test_throws DivideError ZERO  \ x
    @test   ONE  .\ x === x
    @test   ONE   \ x === x
    @test (-ONE) .\ x ≙ -x
    @test (-ONE)  \ x ≙ -x
end
nothing
