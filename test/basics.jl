# Test basics operations on neutral numbers: constructors, accessors, conversions, etc.

using Neutrals
using Neutrals: ≙, ≗, maybe_neutral
using Test
using TypeUtils

@testset "Basics" begin
    # Neutral type and instances.
    @test length(instances(Neutral)) == 3
    @test ZERO ∈ instances(Neutral)
    @test  ONE ∈ instances(Neutral)
    @test -ONE ∈ instances(Neutral)
    @test_throws Exception Neutral(-2)
    @test_throws Exception Neutral("1")
    @test repr(ZERO) == "𝟘"
    @test repr(ONE) == "𝟙"
    @test repr(-ONE) == "-𝟙"
    if VERSION ≥ v"1.3"
        @test ZERO === eval(Meta.parse("𝟘"))
        @test  ONE === eval(Meta.parse("𝟙"))
        @test -ONE === eval(Meta.parse("-𝟙"))
    end
    @test @inferred(typemin(Neutral)) === -ONE
    @test @inferred(typemax(Neutral)) ===  ONE
    @test @inferred(   zero(Neutral)) === ZERO
    @test @inferred(    one(Neutral)) ===  ONE

    # Tests involving `x`, one of the neutral instance, and `v`, its integer value. These
    # tests are wrapped in an `@eval` block so that the values of `x` and `v` are explicitly
    # shown in error messages.
    for (v, x) in (0 => ZERO, 1 => ONE, -1 => -ONE)
        @eval begin
            # Consistency and accessor.
            @test $x ∈ instances(Neutral)
            @test @inferred(Int($x)                   ) === $v
            @test @inferred(Neutrals.value($x)        ) === $v
            @test @inferred(Neutrals.value(typeof($x))) === $v

            # Constructors.
            @test @inferred(Neutral{$v}()         ) === $x
            @test @inferred(Neutral($x)           ) === $x
            @test @inferred(Neutral{$v}($x)       ) === $x
            @test @inferred(Neutral{$v}(Int8($v)) ) === $x
            @test @inferred(Neutral{$v}(float($v))) === $x
            @test           Neutral($v)             === $x # not inferable
            @test           Neutral(Int8($v))       === $x # not inferable
            @test           Neutral(float($v))      === $x # not inferable
            @test_throws Exception Neutral{Int8($v)}()
            for o in instances(Neutral)
                o === $x && continue
                @test_throws InexactError typeof($x)(o)
            end

            # Conversion.
            @test @inferred(convert(typeof($x), $x)) === $x
            @test @inferred(convert(Neutral, $x)   ) === $x
            @test @inferred(typeof($x)($x)         ) === $x
            @test @inferred(convert(Integer, $x)   ) === $x
            @test @inferred(Integer($x)            ) === $x
            @test @inferred(Number($x)             ) === $x
            @test @inferred(Real($x)               ) === $x
            @test @inferred(AbstractFloat($x)      ) === float($v)
            @test @inferred(Rational($x)           ) === $v//1
            @test @inferred(Complex($x)            ) === $v + 0im
            @test_throws InexactError AbstractIrrational($x)

            # Traits.
            @test @inferred(is_static_number(       $x )) === true
            @test @inferred(is_static_number(typeof($x))) === true
            @test @inferred(is_signed(       $x )) === true
            @test @inferred(is_signed(typeof($x))) === true
            @test @inferred(typemin(       $x )) === $x
            @test @inferred(typemin(typeof($x))) === $x
            @test @inferred(typemax(       $x )) === $x
            @test @inferred(typemax(typeof($x))) === $x

            # Unary operation.
            @test @inferred(+$x) === $x
            @test @inferred(-$x) === Neutral(-$v)
            @test @inferred(~$x) === (-1 ≤ ~$v ≤ 1 ? Neutral{~$v}() : ~$v)

            # Unary functions.
            @test summary($x) isa String
            @test repr($x) isa String
            @test @inferred(iszero($x)) === iszero($v)
            @test @inferred(isone($x)) === isone($v)
            @test @inferred(isfinite($x)) === true
            @test @inferred(sign($x)) === sign($v)
            @test @inferred(signbit($x)) === signbit($v)
            @test @inferred(abs($x)) === Neutral(abs($v))
            @test @inferred(Base.checked_abs($x)) === Neutral(abs($v))
            @test @inferred(abs2($x)) === Neutral(abs2($v))
            @test @inferred(conj($x)) === $x
            @test @inferred(transpose($x)) === $x
            @test @inferred(adjoint($x)) === $x
            @test @inferred(zero($x)) === ZERO
            @test @inferred(one($x)) === ONE
            @test @inferred(angle($x)) === ($v < 0 ? π : ZERO)
            if iszero($x)
                @test_throws DivideError inv($x)
            else
                @test @inferred(inv($x)) === $x
            end
            @test @inferred(iseven($x)) === iseven($v)
            @test @inferred(isodd($x)) === isodd($v)
            @test @inferred(modf($x)) === (ZERO, $x)
            @test @inferred(widen($x)) === $x
            @test @inferred(widen(typeof($x))) === typeof($x)

            # Precision.
            @test @inferred(get_precision($x)) == AbstractFloat
            @test @inferred(get_precision(typeof($x))) == AbstractFloat
            @test @inferred(adapt_precision(Float32, $x)) === $x
            @test @inferred(adapt_precision(Float64, $x)) === $x
            @test @inferred(adapt_precision(Float32, typeof($x))) === typeof($x)
            @test @inferred(adapt_precision(Float64, typeof($x))) === typeof($x)

            # Multipliers.
            let A = Float32[]
                @test @inferred(adapt_multiplier_precision($x, A)        ) === $x
                @test @inferred(adapt_multiplier_precision($x, typeof(A))) === $x
                @test @inferred(adapt_multiplier_precision(eltype(A), $x)) === $x
            end

            # Dispatch on neutrals.
            @test @inferred(Neutrals.dispatch($x)) === $x
        end
    end

    # Conversions or neutral numbers to another numeric type.
    for T ∈ [Integer,
             Bool,
             Int8, Int16, Int32, Int64, Int128, BigInt,
             UInt8, UInt16, UInt32, UInt64, UInt128,
             AbstractFloat,
             Float16, Float32, Float64, BigFloat,
             Rational, Rational{Bool}, Rational{Int8}, Rational{UInt8},
             Complex{Bool}, Complex{Int16}, Complex{UInt16}, Complex{Float32}]
        for x ∈ instances(Neutral)
            # `convert(T,x)` and `T(x)` should yield the same result equal to `T(value(x))`
            # except if `x` is `-ONE` and `T` is unsigned in which case an `InexactError`
            # exception is thrown.
            if is_signed(T) || Int(x) ≥ 0 # FIXME is_signed(T) -> !(T <: NonnegativeNumber)
                y = @inferred(T(x))
                @eval begin
                    @test $y isa $T
                    @test $y == $T(Int($x))
                    if $T === AbstractFloat
                        @test $y isa Float64
                        @test $y === float($x)
                    end
                end
                z = if VERSION < v"1.1"
                    # For some reasons this inference is broken in tests with Julia 1.0.
                    convert(T, x)
                else
                    @inferred(convert(T, x))
                end
                @eval begin
                    @test typeof($z) == typeof($y)
                    @test $z == $y
                end
            else
                @eval begin
                    @test_throws InexactError $T($x)
                    @test_throws InexactError convert($T, $x)
                end
            end
            if T <: Integer
                y = @inferred(rem(x, T))
                @eval begin
                    @test $y isa $T
                    @test $y == (Int($x) % $T)
                end
            end
        end
    end

    # Dispatch on other numbers than neutrals.
    @test @inferred(Neutrals.dispatch(π)) === π
    val = 0.0f0
    obj = @inferred(Neutrals.dispatch(val))
    @test obj isa Neutrals.Dispatch{typeof(val)}
    @test eltype(obj) === typeof(val)
    @test eltype(typeof(obj)) === typeof(val)
    @test obj[] === val
    @test @inferred(Neutrals.dispatch(obj)) === obj
    @test @inferred(Neutrals.Dispatch(obj)) === obj
    val = 1//2
    obj = @inferred(Neutrals.dispatch(val))
    @test obj isa Neutrals.Dispatch{typeof(val)}
    @test eltype(obj) === typeof(val)
    @test eltype(typeof(obj)) === typeof(val)
    @test obj[] === val
    @test @inferred(Neutrals.dispatch(obj)) === obj
    @test @inferred(Neutrals.Dispatch(obj)) === obj

    # Macros.
    @testset "Macros" begin
        ex = @macroexpand Neutrals.@dispatch_on_value β unsafe_xpby!(dst, x, β, y)
        @test ex isa Expr
        @test ex.head == :if
    end
end
nothing
