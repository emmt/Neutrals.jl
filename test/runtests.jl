using Neutrals
using Neutrals: infinity, ispositive, isnegative, static_value,
    negate, can_be_truly_negated
using Test
using TypeUtils
using Aqua

@testset "Neutrals package" begin
    same_value_and_type(x::T, y::T) where {T<:Number} =
        isbitstype(T) ? (x === y) : isequal(x, y)
    same_value_and_type(x::T, y::T) where {T} = isequal(x, y)
    same_value_and_type(x, y) = false

    raw_type(x::Number) = raw_type(typeof(x))
    raw_type(::Type{<:Complex{T}}) where {T} = raw_type(T)
    raw_type(::Type{<:Rational{T}}) where {T} = raw_type(T)
    raw_type(::Type{T}) where {T<:Real} = T

    iscomplex(x::Real) = false
    iscomplex(x::Complex) = true
    iscomplex(::Type{<:Real}) = false
    iscomplex(::Type{<:Complex}) = true

    function add_op(::Type{T}, x::Neutral) where {T<:Unsigned}
        v = static_value(x)
        return v < 0 ? -signed(convert(T, -v)) : convert(T, v)
    end
    function add_op(::Type{T}, x::Neutral) where {T<:Bool}
        return Int(static_value(x))::Int
    end
    function add_op(::Type{T}, x::Neutral) where {T<:AbstractIrrational}
        return float(static_value(x))
    end
    function add_op(::Type{T}, x::Neutral) where {S,T<:Union{Rational{S},Complex{S}}}
        return add_op(S, x)
    end
    function add_op(::Type{T}, x::Neutral) where {T<:Union{BigInt,BigFloat}}
        v = static_value(x)
        return v < 0 ? Clong(v) : Culong(v)
    end
    function add_op(::Type{T}, x::Neutral) where {T<:Real}
        return convert(T, static_value(x))
    end

    maybe_neutral(x::Int) = -1 <= x <= 1 ? Neutral{x}() : x

    add(x::Neutral, y::Neutral) = maybe_neutral(static_value(x) + static_value(y))
    add(x::Neutral, y::Union{Real,Complex}) = add(y, x)
    add(x::Union{Real,Complex}, y::Neutral) =
        iszero(y) ? x : x + add_op(typeof(x), y)

    sub(x::Neutral, y::Neutral) = maybe_neutral(static_value(x) - static_value(y))
    sub(x::Neutral, y::Union{Real,Complex}) =
        iszero(x) ? -y : add_op(typeof(y), x) - y
    sub(x::Union{Real,Complex}, y::Neutral) =
        iszero(y) ? x : x - add_op(typeof(x), y)

    @testset "Constants" begin
        @test typeof(ZERO) === Neutral{ 0}
        @test typeof( ONE) === Neutral{ 1}
        @test typeof(-ONE) === Neutral{-1}
    end

    @testset "Non-exported public API" begin
        @test @inferred(static_value(ZERO)) ===  0
        @test @inferred(static_value( ONE)) ===  1
        @test @inferred(static_value(-ONE)) === -1

        @test @inferred(infinity(0)) === Inf
        @test @inferred(infinity(4)) === Inf
        @test @inferred(infinity(-2)) === -Inf
        @test @inferred(infinity(0//1)) === 1//0
        @test @inferred(infinity(2//1)) === 1//0
        @test @inferred(infinity(-3//1)) === -1//0
        @test @inferred(infinity(1 - im)) === complex(Inf, -Inf)

        @test @inferred(can_be_truly_negated(true)) === true
        @test @inferred(can_be_truly_negated(false)) === true
        @test @inferred(can_be_truly_negated(1)) === true
        @test @inferred(can_be_truly_negated(1.0)) === true
        @test @inferred(can_be_truly_negated(-2 + im)) === true
        @test @inferred(can_be_truly_negated(π)) === true
        @test @inferred(can_be_truly_negated(0x00)) === true
        @test @inferred(can_be_truly_negated(0x01)) === false
        @test @inferred(can_be_truly_negated(0x00//0x01)) === true
        @test @inferred(can_be_truly_negated(0x03//0x02)) === false
        @test @inferred(can_be_truly_negated(0x00 + 0x00*im)) === true
        @test @inferred(can_be_truly_negated(0x03 + 0x02*im)) === false

        @test @inferred(negate(true)) === -1
        @test @inferred(negate(false)) === 0
        @test @inferred(negate(1)) === -1
        @test @inferred(negate(-1.0)) === 1.0
        @test @inferred(negate(-2 + im)) === 2 - im
        @test @inferred(negate(π)) === -π
        @test @inferred(negate(0x00)) === 0x00
        @test @inferred(negate(0x00//0x01)) === 0x00//0x01
        @test @inferred(negate(0x00 + 0x00*im)) === 0x00 + 0x00*im

        @test_throws OverflowError negate(0x01)
        @test_throws OverflowError negate(0x03//0x02)
        @test_throws OverflowError negate(0x03 + 0x02*im)
    end

    @testset "Basic methods on neutral" begin
        @test sprint(show, ZERO) == (VERSION ≥ v"1.3" ?  "𝟘" : "ZERO")
        @test sprint(show,  ONE) == (VERSION ≥ v"1.3" ?  "𝟙" :  "ONE")
        @test sprint(show, -ONE) == (VERSION ≥ v"1.3" ? "-𝟙" : "-ONE")

        @test startswith(summary(ZERO), "neutral element for the addition")
        @test startswith(summary( ONE), "neutral element for the multiplication")
        @test startswith(summary(-ONE), "opposite of neutral element for the multiplication")

        @test sprint(summary, ZERO) == summary(ZERO)
        @test sprint(summary,  ONE) == summary( ONE)
        @test sprint(summary, -ONE) == summary(-ONE)

        @test @inferred(zero(ZERO)) === ZERO
        @test @inferred(zero( ONE)) === ZERO
        @test @inferred(zero(-ONE)) === ZERO

        @test @inferred(one(ZERO)) === ONE
        @test @inferred(one( ONE)) === ONE
        @test @inferred(one(-ONE)) === ONE

        @test @inferred(oneunit(ZERO)) === ONE
        @test @inferred(oneunit( ONE)) === ONE
        @test @inferred(oneunit(-ONE)) === ONE

        @test @inferred(iszero(ZERO)) === true
        @test @inferred(iszero( ONE)) === false
        @test @inferred(iszero(-ONE)) === false

        @test @inferred(isone(ZERO)) === false
        @test @inferred(isone( ONE)) === true
        @test @inferred(isone(-ONE)) === false

        @test @inferred(ispositive(ZERO)) === false
        @test @inferred(ispositive( ONE)) === true
        @test @inferred(ispositive(-ONE)) === false

        @test @inferred(isnegative(ZERO)) === false
        @test @inferred(isnegative( ONE)) === false
        @test @inferred(isnegative(-ONE)) === true

        @test @inferred(signbit(ZERO)) === false
        @test @inferred(signbit( ONE)) === false
        @test @inferred(signbit(-ONE)) === true

        @test @inferred(abs(ZERO)) === ZERO
        @test @inferred(abs( ONE)) ===  ONE
        @test @inferred(abs(-ONE)) ===  ONE

        @test @inferred(abs2(ZERO)) === ZERO
        @test @inferred(abs2( ONE)) ===  ONE
        @test @inferred(abs2(-ONE)) ===  ONE

        @test @inferred(Base.checked_abs(ZERO)) === ZERO
        @test @inferred(Base.checked_abs( ONE)) ===  ONE
        @test @inferred(Base.checked_abs(-ONE)) ===  ONE

        @test @inferred(iseven(ZERO)) === true
        @test @inferred(iseven( ONE)) === false
        @test @inferred(iseven(-ONE)) === false

        @test @inferred(isodd(ZERO)) === false
        @test @inferred(isodd( ONE)) === true
        @test @inferred(isodd(-ONE)) === true

        @test @inferred(angle(ZERO)) === ZERO
        @test @inferred(angle( ONE)) === ZERO
        @test @inferred(angle(-ONE)) === π

        @test @inferred(inv(ZERO)) ===  Inf
        @test @inferred(inv( ONE)) ===  ONE
        @test @inferred(inv(-ONE)) === -ONE
    end

    @testset "Unary operators on neutral" begin
        @test @inferred(-(ZERO)) === ZERO
        @test @inferred(-( ONE)) === -ONE
        @test @inferred(-(-ONE)) ===  ONE

        @test @inferred(~(ZERO)) === -ONE
        @test @inferred(~( ONE)) ===   -2
        @test @inferred(~(-ONE)) === ZERO
    end

    @testset "Conversion to `$T`" for T in (Number, Real, Integer, Neutral)
        @test @inferred(T(ZERO)) === ZERO
        @test @inferred(T( ONE)) ===  ONE
        @test @inferred(T(-ONE)) === -ONE

        @test @inferred(convert(T, ZERO)) === ZERO
        @test @inferred(convert(T,  ONE)) ===  ONE
        @test @inferred(convert(T, -ONE)) === -ONE
    end

    @testset "Conversion to `Signed`" begin
        @test @inferred(Signed(ZERO)) ===  0
        @test @inferred(Signed( ONE)) ===  1
        @test @inferred(Signed(-ONE)) === -1

        @test @inferred(convert(Signed, ZERO)) ===  0
        @test @inferred(convert(Signed,  ONE)) ===  1
        @test @inferred(convert(Signed, -ONE)) === -1
    end

    @testset "Conversion to `Unsigned`" begin
        @test @inferred(Unsigned(ZERO)) ===  UInt(0)
        @test @inferred(Unsigned( ONE)) ===  UInt(1)
        @test_throws InexactError Unsigned(-ONE)

        @test @inferred(convert(Unsigned,ZERO)) ===  UInt(0)
        @test @inferred(convert(Unsigned, ONE)) ===  UInt(1)
        @test_throws InexactError convert(Unsigned, -ONE)
    end

    @testset "Conversion to `Rational`" begin
        @test @inferred(Rational(ZERO)) ===  0//1
        @test @inferred(Rational( ONE)) ===  1//1
        @test @inferred(Rational(-ONE)) === -1//1

        @test @inferred(convert(Rational, ZERO)) ===  0//1
        @test @inferred(convert(Rational,  ONE)) ===  1//1
        @test @inferred(convert(Rational, -ONE)) === -1//1

        @test @inferred(Rational{Int16}(ZERO)) === Rational{Int16}( 0, 1)
        @test @inferred(Rational{Int16}( ONE)) === Rational{Int16}( 1, 1)
        @test @inferred(Rational{Int16}(-ONE)) === Rational{Int16}(-1, 1)

        @test @inferred(convert(Rational{Int16}, ZERO)) === Rational{Int16}( 0, 1)
        @test @inferred(convert(Rational{Int16},  ONE)) === Rational{Int16}( 1, 1)
        @test @inferred(convert(Rational{Int16}, -ONE)) === Rational{Int16}(-1, 1)
    end

    @testset "Conversion to `AbstractFloat`" begin
        @test @inferred(AbstractFloat(ZERO)) ===  0.0
        @test @inferred(AbstractFloat( ONE)) ===  1.0
        @test @inferred(AbstractFloat(-ONE)) === -1.0

        @test @inferred(convert(AbstractFloat, ZERO)) ===  0.0
        @test @inferred(convert(AbstractFloat,  ONE)) ===  1.0
        @test @inferred(convert(AbstractFloat, -ONE)) === -1.0

        @test @inferred(float(ZERO)) ===  0.0
        @test @inferred(float( ONE)) ===  1.0
        @test @inferred(float(-ONE)) === -1.0
    end

    @testset "Conversion to `Complex`" begin
        @test @inferred(Complex(ZERO)) === Complex{Bool}(false, false)
        @test @inferred(Complex( ONE)) === Complex{Bool}(true, false)
        @test @inferred(Complex(-ONE)) === Complex{Int}(-1, 0)

        @test @inferred(convert(Complex, ZERO)) === Complex{Bool}(false, false)
        @test @inferred(convert(Complex,  ONE)) === Complex{Bool}(true, false)
        @test @inferred(convert(Complex, -ONE)) === Complex{Int}(-1, 0)

        @test @inferred(Complex{Float32}(ZERO)) === Complex{Float32}( 0, 0)
        @test @inferred(Complex{Float32}( ONE)) === Complex{Float32}( 1, 0)
        @test @inferred(Complex{Float32}(-ONE)) === Complex{Float32}(-1, 0)

        @test @inferred(convert(Complex{Float32}, ZERO)) === Complex{Float32}( 0, 0)
        @test @inferred(convert(Complex{Float32},  ONE)) === Complex{Float32}( 1, 0)
        @test @inferred(convert(Complex{Float32}, -ONE)) === Complex{Float32}(-1, 0)
    end

    @testset "Conversion to `Int`" begin
        @test @inferred(Int(ZERO)) ===  0
        @test @inferred(Int( ONE)) ===  1
        @test @inferred(Int(-ONE)) === -1

        @test @inferred(convert(Int, ZERO)) ===  0
        @test @inferred(convert(Int,  ONE)) ===  1
        @test @inferred(convert(Int, -ONE)) === -1
    end

    @testset "Conversion to `Bool`" begin
        @test @inferred(Bool(ZERO)) === false
        @test @inferred(Bool( ONE)) === true
        @test_throws InexactError Bool(-ONE)

        @test @inferred(convert(Bool,ZERO)) === false
        @test @inferred(convert(Bool, ONE)) === true
        @test_throws InexactError convert(Bool, -ONE)
    end

    @testset "Conversion to `BigInt`" begin
        let x = @inferred(BigInt(ZERO))
            @test x isa BigInt
            @test x == 0
        end
        let x = @inferred(BigInt(ONE))
            @test x isa BigInt
            @test x == 1
        end
        let x = @inferred(BigInt(-ONE))
            @test x isa BigInt
            @test x == -1
        end

        let x = @inferred(big(ZERO))
            @test x isa BigInt
            @test x == 0
        end
        let x = @inferred(big(ONE))
            @test x isa BigInt
            @test x == 1
        end
        let x = @inferred(big(-ONE))
            @test x isa BigInt
            @test x == -1
        end
    end

    @testset "Conversion to `BigFloat`" begin
        let x = @inferred(BigFloat(ZERO))
            @test x isa BigFloat
            @test x == 0
        end
        let x = @inferred(BigFloat(ONE))
            @test x isa BigFloat
            @test x == 1
        end
        let x = @inferred(BigFloat(-ONE))
            @test x isa BigFloat
            @test x == -1
        end
    end

    @testset "Conversion to `AbstractIrrational`" begin
        @test_throws InexactError typeof(π)(ZERO)
        @test_throws InexactError typeof(π)( ONE)
        @test_throws InexactError typeof(π)(-ONE)
        @test_throws InexactError convert(typeof(π), ZERO)
        @test_throws InexactError convert(typeof(π),  ONE)
        @test_throws InexactError convert(typeof(π), -ONE)
    end

    @testset "Outer constructors" begin
        @test @inferred(Neutral{ 0}()) === ZERO
        @test @inferred(Neutral{ 1}()) ===  ONE
        @test @inferred(Neutral{-1}()) === -ONE

        @test @inferred(Neutral(ZERO)) === ZERO
        @test @inferred(Neutral( ONE)) ===  ONE
        @test @inferred(Neutral(-ONE)) === -ONE

        @test Neutral( 0) === ZERO
        @test Neutral( 1) ===  ONE
        @test Neutral(-1) === -ONE

        @test Neutral( UInt8(0)) === ZERO
        @test Neutral( Int16(1)) ===  ONE
        @test Neutral(-Int16(1)) === -ONE

        @test_throws ArgumentError Neutral(+2)
        @test_throws ArgumentError Neutral(-2)

        @test_throws InexactError typeof(π)( ONE)
        @test_throws InexactError typeof(π)(-ONE)
        @test_throws InexactError convert(typeof(π), ZERO)
        @test_throws InexactError convert(typeof(π),  ONE)
        @test_throws InexactError convert(typeof(π), -ONE)
    end

    @testset "Test `TypeUtils` methods" begin
        @test @inferred(is_signed(ZERO)) === true
        @test @inferred(is_signed( ONE)) === true
        @test @inferred(is_signed(-ONE)) === true

        @test @inferred(is_static_number(ZERO)) === true
        @test @inferred(is_static_number( ONE)) === true
        @test @inferred(is_static_number(-ONE)) === true

        @test @inferred(get_precision(ZERO)) === AbstractFloat
        @test @inferred(get_precision( ONE)) === AbstractFloat
        @test @inferred(get_precision(-ONE)) === AbstractFloat

        @test @inferred(adapt_precision(Float32,  ZERO)) === ZERO
        @test @inferred(adapt_precision(Float64,   ONE)) ===  ONE
        @test @inferred(adapt_precision(BigFloat, -ONE)) === -ONE

        @test @inferred(adapt_precision(Float32,  typeof(ZERO))) === typeof(ZERO)
        @test @inferred(adapt_precision(Float64,  typeof( ONE))) === typeof( ONE)
        @test @inferred(adapt_precision(BigFloat, typeof(-ONE))) === typeof(-ONE)
    end

    bits_unsigned = [UInt8, UInt16, UInt32, UInt64]
    isdefined(Base, :UInt128) && push!(bits_unsigned, UInt128)
    bits_signed = [Int8, Int16, Int32, Int64]
    isdefined(Base, :Int128) && push!(bits_unsigned, Int128)
    bits_float = [Float16, Float32, Float64]
    bits_integer = vcat(Bool, bits_unsigned, bits_signed)
    bits_real = vcat(bits_integer, bits_float)

    @testset "Conversion to `$T`" for T in bits_real
        @test @inferred(T(ZERO)) === (T(0)::T)
        @test @inferred(convert(T, ZERO)) === (T(0)::T)

        @test @inferred(T(ONE)) === (T(1)::T)
        @test @inferred(convert(T, ONE)) === (T(1)::T)

        if T <: Union{Bool,Unsigned}
            @test_throws InexactError T(-ONE)
            @test_throws InexactError convert(T, -ONE)
        else
            @test @inferred(T(-ONE)) === (T(-1)::T)
            @test @inferred(convert(T, -ONE)) === (T(-1)::T)
        end
    end

    @testset "Promotion rules for T=$T" for T in [
        bits_integer..., BigInt, bits_float..., BigFloat]
        Tp = T <: Bool ? Int : T
        @test @inferred(promote_rule(Neutral,     T)) === Tp
        @test @inferred(promote_rule(Neutral{ 0}, T)) === Tp
        @test @inferred(promote_rule(Neutral{ 1}, T)) === Tp
        @test @inferred(promote_rule(Neutral{-1}, T)) === Tp
    end

    @testset "Ranges" begin
        @test @inferred(ZERO:ZERO) === 0: 0
        @test @inferred(ZERO: ONE) === 0: 1
        @test @inferred(ZERO:-ONE) === 0:-1
        @test @inferred( ONE:ZERO) === Base.OneTo( 0)
        @test @inferred( ONE: ONE) === Base.OneTo( 1)
        @test @inferred( ONE:-ONE) === Base.OneTo(-1)
        @test @inferred(-ONE:ZERO) === -1: 0
        @test @inferred(-ONE: ONE) === -1: 1
        @test @inferred(-ONE:-ONE) === -1:-1

        @test @inferred(ZERO:2) ===  0:2
        @test @inferred( ONE:2) === Base.OneTo(2)
        @test @inferred(-ONE:2) === -1:2
        @test @inferred(ZERO:0x02) ===  0x00:0x02
        @test @inferred( ONE:0x02) === Base.OneTo(0x02)
        @test_throws InexactError -ONE:0x02
        @test @inferred(ZERO:3.0f0) ===  0.0f0:3.0f0
        @test @inferred( ONE:3.0f0) ===  1.0f0:3.0f0
        @test @inferred(-ONE:3.0f0) === -1.0f0:3.0f0

        # `start:𝟘:stop` throws
        @test_throws ArgumentError ZERO:ZERO:ZERO
        @test_throws ArgumentError ZERO:ZERO: ONE
        @test_throws ArgumentError ZERO:ZERO:-ONE
        @test_throws ArgumentError  ONE:ZERO:ZERO
        @test_throws ArgumentError  ONE:ZERO: ONE
        @test_throws ArgumentError  ONE:ZERO:-ONE
        @test_throws ArgumentError -ONE:ZERO:ZERO
        @test_throws ArgumentError -ONE:ZERO: ONE
        @test_throws ArgumentError -ONE:ZERO:-ONE
        @test_throws ArgumentError true:ZERO:true
        @test_throws ArgumentError 1:ZERO:1
        @test_throws ArgumentError 1.0:ZERO:1.0
        @test_throws ArgumentError 0:ZERO:1.0

        # `start:𝟙:stop` yields `start:stop`
        @test @inferred(ZERO: ONE:ZERO) === ZERO:ZERO
        @test @inferred(ZERO: ONE: ONE) === ZERO: ONE
        @test @inferred(ZERO: ONE:-ONE) === ZERO:-ONE
        @test @inferred( ONE: ONE:ZERO) ===  ONE:ZERO
        @test @inferred( ONE: ONE: ONE) ===  ONE: ONE
        @test @inferred( ONE: ONE:-ONE) ===  ONE:-ONE
        @test @inferred(-ONE: ONE:ZERO) === -ONE:ZERO
        @test @inferred(-ONE: ONE: ONE) === -ONE: ONE
        @test @inferred(-ONE: ONE:-ONE) === -ONE:-ONE

        @test @inferred(ZERO:ONE:2) ===  0:2
        @test @inferred( ONE:ONE:2) === Base.OneTo(2)
        @test @inferred(-ONE:ONE:2) === -1:2
        @test @inferred(ZERO:ONE:0x02) ===  0x00:0x02
        @test @inferred( ONE:ONE:0x02) === Base.OneTo(0x02)
        @test_throws InexactError -ONE:ONE:0x02
        @test @inferred(ZERO:ONE:3.0f0) ===  0.0f0:3.0f0
        @test @inferred( ONE:ONE:3.0f0) ===  1.0f0:3.0f0
        @test @inferred(-ONE:ONE:3.0f0) === -1.0f0:3.0f0

        # `start:-𝟙:stop` yields `start:-1:stop`
        @test @inferred(ZERO:-ONE:ZERO) ===  0:-1: 0
        @test @inferred(ZERO:-ONE: ONE) ===  0:-1: 1
        @test @inferred(ZERO:-ONE:-ONE) ===  0:-1:-1
        @test @inferred( ONE:-ONE:ZERO) ===  1:-1: 0
        @test @inferred( ONE:-ONE: ONE) ===  1:-1: 1
        @test @inferred( ONE:-ONE:-ONE) ===  1:-1:-1
        @test @inferred(-ONE:-ONE:ZERO) === -1:-1: 0
        @test @inferred(-ONE:-ONE: ONE) === -1:-1: 1
        @test @inferred(-ONE:-ONE:-ONE) === -1:-1:-1

        @test @inferred(ZERO:-ONE:-2) ===  0:-1:-2
        @test @inferred( ONE:-ONE:-2) ===  1:-1:-2
        @test @inferred(-ONE:-ONE:-2) === -1:-1:-2
        @test @inferred(ZERO:-ONE:0x02) === 0x00:-Int8(1):0x02
        @test @inferred( ONE:-ONE:0x02) === 0x01:-Int8(1):0x02
        @test_throws InexactError -ONE:-ONE:0x02
        @test @inferred(ZERO:-ONE:3.0f0) ===  0.0f0:-1.0f0:3.0f0
        @test @inferred( ONE:-ONE:3.0f0) ===  1.0f0:-1.0f0:3.0f0
        @test @inferred(-ONE:-ONE:3.0f0) === -1.0f0:-1.0f0:3.0f0

        # Special cases.
        let r = @inferred(Base.OneTo(ZERO))
            @test r isa Base.OneTo{typeof(ZERO)}
            @test @inferred(isempty(r)) === true
            @test @inferred(length(r)) === 0
            @test @inferred(first(r)) === ONE
            @test @inferred(last(r)) === ZERO
        end
        let r = @inferred(Base.OneTo(ONE))
            @test r isa Base.OneTo{typeof(ONE)}
            @test @inferred(isempty(r)) === false
            @test @inferred(length(r)) === 1
            @test @inferred(first(r)) === ONE
            @test @inferred(last(r)) === ONE
        end
        @test_throws InexactError Base.OneTo(-ONE)
    end

    @testset "Arithmetic on neutral numbers" begin
        @test @inferred( ZERO  +  ZERO ) === ZERO
        @test @inferred( ZERO  +   ONE ) ===  ONE
        @test @inferred( ZERO  + (-ONE)) === -ONE
        @test @inferred(  ONE  +  ZERO ) ===  ONE
        @test @inferred(  ONE  +   ONE ) ===    2
        @test @inferred(  ONE  + (-ONE)) === ZERO
        @test @inferred((-ONE) +  ZERO ) === -ONE
        @test @inferred((-ONE) +   ONE ) === ZERO
        @test @inferred((-ONE) + (-ONE)) ===   -2

        @test @inferred( ZERO  -  ZERO ) === ZERO
        @test @inferred( ZERO  -   ONE ) === -ONE
        @test @inferred( ZERO  - (-ONE)) ===  ONE
        @test @inferred(  ONE  -  ZERO ) ===  ONE
        @test @inferred(  ONE  -   ONE ) === ZERO
        @test @inferred(  ONE  - (-ONE)) ===    2
        @test @inferred((-ONE) -  ZERO ) === -ONE
        @test @inferred((-ONE) -   ONE ) ===   -2
        @test @inferred((-ONE) - (-ONE)) === ZERO

        @test @inferred( ZERO  *  ZERO ) === ZERO
        @test @inferred( ZERO  *   ONE ) === ZERO
        @test @inferred( ZERO  * (-ONE)) === ZERO
        @test @inferred(  ONE  *  ZERO ) === ZERO
        @test @inferred(  ONE  *   ONE ) ===  ONE
        @test @inferred(  ONE  * (-ONE)) === -ONE
        @test @inferred((-ONE) *  ZERO ) === ZERO
        @test @inferred((-ONE) *   ONE ) === -ONE
        @test @inferred((-ONE) * (-ONE)) ===  ONE

        @test @inferred( ZERO  /  ZERO ) === NaN
        @test @inferred( ZERO  /   ONE ) === ZERO
        @test @inferred( ZERO  / (-ONE)) === ZERO
        @test @inferred(  ONE  /  ZERO ) === Inf
        @test @inferred(  ONE  /   ONE ) === ONE
        @test @inferred(  ONE  / (-ONE)) === -ONE
        @test @inferred((-ONE) /  ZERO ) === -Inf
        @test @inferred((-ONE) /   ONE ) === -ONE
        @test @inferred((-ONE) / (-ONE)) === ONE

        @test @inferred( ZERO  \  ZERO ) ===  ZERO  /  ZERO
        @test @inferred( ZERO  \   ONE ) ===   ONE  /  ZERO
        @test @inferred( ZERO  \ (-ONE)) === (-ONE) /  ZERO
        @test @inferred(  ONE  \  ZERO ) ===  ZERO  /   ONE
        @test @inferred(  ONE  \   ONE ) ===   ONE  /   ONE
        @test @inferred(  ONE  \ (-ONE)) === (-ONE) /   ONE
        @test @inferred((-ONE) \  ZERO ) ===  ZERO  / (-ONE)
        @test @inferred((-ONE) \   ONE ) ===   ONE  / (-ONE)
        @test @inferred((-ONE) \ (-ONE)) === (-ONE) / (-ONE)

        @test @inferred( ZERO  //  ZERO ) === NaN
        @test @inferred( ZERO  //   ONE ) === ZERO
        @test @inferred( ZERO  // (-ONE)) === ZERO
        @test @inferred(  ONE  //  ZERO ) === 1//0
        @test @inferred(  ONE  //   ONE ) === ONE
        @test @inferred(  ONE  // (-ONE)) === -ONE
        @test @inferred((-ONE) //  ZERO ) === -1//0
        @test @inferred((-ONE) //   ONE ) === -ONE
        @test @inferred((-ONE) // (-ONE)) === ONE

    end

    @testset "Bitwise operations on neutral numbers" begin
        # Bitwise OR.
        @test @inferred( ZERO  |  ZERO ) === ZERO
        @test @inferred( ZERO  |   ONE ) ===  ONE
        @test @inferred( ZERO  | (-ONE)) === -ONE
        @test @inferred(  ONE  |  ZERO ) ===  ONE
        @test @inferred(  ONE  |   ONE ) ===  ONE
        @test @inferred(  ONE  | (-ONE)) === -ONE
        @test @inferred((-ONE) |  ZERO ) === -ONE
        @test @inferred((-ONE) |   ONE ) === -ONE
        @test @inferred((-ONE) | (-ONE)) === -ONE

        # Bitwise AND.
        @test @inferred( ZERO  &  ZERO ) === ZERO
        @test @inferred( ZERO  &   ONE ) === ZERO
        @test @inferred( ZERO  & (-ONE)) === ZERO
        @test @inferred(  ONE  &  ZERO ) === ZERO
        @test @inferred(  ONE  &   ONE ) ===  ONE
        @test @inferred(  ONE  & (-ONE)) ===  ONE
        @test @inferred((-ONE) &  ZERO ) === ZERO
        @test @inferred((-ONE) &   ONE ) ===  ONE
        @test @inferred((-ONE) & (-ONE)) === -ONE

        # Bitwise XOR.
        @test @inferred( ZERO  ⊻  ZERO ) === ZERO
        @test @inferred( ZERO  ⊻   ONE ) ===  ONE
        @test @inferred( ZERO  ⊻ (-ONE)) === -ONE
        @test @inferred(  ONE  ⊻  ZERO ) ===  ONE
        @test @inferred(  ONE  ⊻   ONE ) === ZERO
        @test @inferred(  ONE  ⊻ (-ONE)) ===   -2
        @test @inferred((-ONE) ⊻  ZERO ) === -ONE
        @test @inferred((-ONE) ⊻   ONE ) ===   -2
        @test @inferred((-ONE) ⊻ (-ONE)) === ZERO
    end

    @testset "Bit-shift operations on neutral numbers" begin
        @test @inferred( ZERO  <<  ZERO ) === ZERO
        @test @inferred( ZERO  <<   ONE ) === ZERO
        @test @inferred( ZERO  << (-ONE)) === ZERO
        @test @inferred(  ONE  <<  ZERO ) ===  ONE
        @test @inferred(  ONE  <<   ONE ) ===    2
        @test @inferred(  ONE  << (-ONE)) === ZERO
        @test @inferred((-ONE) <<  ZERO ) === -ONE
        @test @inferred((-ONE) <<   ONE ) ===   -2
        @test @inferred((-ONE) << (-ONE)) === -ONE

        @test @inferred( ZERO  >>  ZERO ) === ZERO
        @test @inferred( ZERO  >>   ONE ) === ZERO
        @test @inferred( ZERO  >> (-ONE)) === ZERO
        @test @inferred(  ONE  >>  ZERO ) ===  ONE
        @test @inferred(  ONE  >>   ONE ) === ZERO
        @test @inferred(  ONE  >> (-ONE)) ===    2
        @test @inferred((-ONE) >>  ZERO ) === -ONE
        @test @inferred((-ONE) >>   ONE ) === -ONE
        @test @inferred((-ONE) >> (-ONE)) ===   -2

        @test @inferred( ZERO  >>>  ZERO ) === ZERO
        @test @inferred( ZERO  >>>   ONE ) === ZERO
        @test @inferred( ZERO  >>> (-ONE)) === ZERO
        @test @inferred(  ONE  >>>  ZERO ) ===  ONE
        @test @inferred(  ONE  >>>   ONE ) === ZERO
        @test @inferred(  ONE  >>> (-ONE)) ===    2
        @test @inferred((-ONE) >>>  ZERO ) === -ONE
        @test @inferred((-ONE) >>>   ONE ) === ((-1) >>> 1)
        @test @inferred((-ONE) >>> (-ONE)) ===   -2
    end

    @testset "Comparisons on neutral numbers" begin
        @test @inferred(( ZERO  ==  ZERO )) === ( 0 ==  0)
        @test @inferred(( ZERO  ==   ONE )) === ( 0 ==  1)
        @test @inferred(( ZERO  == (-ONE))) === ( 0 == -1)
        @test @inferred((  ONE  ==  ZERO )) === ( 1 ==  0)
        @test @inferred((  ONE  ==   ONE )) === ( 1 ==  1)
        @test @inferred((  ONE  == (-ONE))) === ( 1 == -1)
        @test @inferred(((-ONE) ==  ZERO )) === (-1 ==  0)
        @test @inferred(((-ONE) ==   ONE )) === (-1 ==  1)
        @test @inferred(((-ONE) == (-ONE))) === (-1 == -1)

        @test @inferred(( ZERO  <  ZERO )) === ( 0 <  0)
        @test @inferred(( ZERO  <   ONE )) === ( 0 <  1)
        @test @inferred(( ZERO  < (-ONE))) === ( 0 < -1)
        @test @inferred((  ONE  <  ZERO )) === ( 1 <  0)
        @test @inferred((  ONE  <   ONE )) === ( 1 <  1)
        @test @inferred((  ONE  < (-ONE))) === ( 1 < -1)
        @test @inferred(((-ONE) <  ZERO )) === (-1 <  0)
        @test @inferred(((-ONE) <   ONE )) === (-1 <  1)
        @test @inferred(((-ONE) < (-ONE))) === (-1 < -1)

        @test @inferred(( ZERO  <=  ZERO )) === ( 0 <=  0)
        @test @inferred(( ZERO  <=   ONE )) === ( 0 <=  1)
        @test @inferred(( ZERO  <= (-ONE))) === ( 0 <= -1)
        @test @inferred((  ONE  <=  ZERO )) === ( 1 <=  0)
        @test @inferred((  ONE  <=   ONE )) === ( 1 <=  1)
        @test @inferred((  ONE  <= (-ONE))) === ( 1 <= -1)
        @test @inferred(((-ONE) <=  ZERO )) === (-1 <=  0)
        @test @inferred(((-ONE) <=   ONE )) === (-1 <=  1)
        @test @inferred(((-ONE) <= (-ONE))) === (-1 <= -1)

        @test @inferred(( ZERO  >  ZERO )) === ( 0 >  0)
        @test @inferred(( ZERO  >   ONE )) === ( 0 >  1)
        @test @inferred(( ZERO  > (-ONE))) === ( 0 > -1)
        @test @inferred((  ONE  >  ZERO )) === ( 1 >  0)
        @test @inferred((  ONE  >   ONE )) === ( 1 >  1)
        @test @inferred((  ONE  > (-ONE))) === ( 1 > -1)
        @test @inferred(((-ONE) >  ZERO )) === (-1 >  0)
        @test @inferred(((-ONE) >   ONE )) === (-1 >  1)
        @test @inferred(((-ONE) > (-ONE))) === (-1 > -1)

        @test @inferred(( ZERO  >=  ZERO )) === ( 0 >=  0)
        @test @inferred(( ZERO  >=   ONE )) === ( 0 >=  1)
        @test @inferred(( ZERO  >= (-ONE))) === ( 0 >= -1)
        @test @inferred((  ONE  >=  ZERO )) === ( 1 >=  0)
        @test @inferred((  ONE  >=   ONE )) === ( 1 >=  1)
        @test @inferred((  ONE  >= (-ONE))) === ( 1 >= -1)
        @test @inferred(((-ONE) >=  ZERO )) === (-1 >=  0)
        @test @inferred(((-ONE) >=   ONE )) === (-1 >=  1)
        @test @inferred(((-ONE) >= (-ONE))) === (-1 >= -1)

        @test @inferred(cmp( ZERO,   ZERO )) === cmp( 0,  0)
        @test @inferred(cmp( ZERO,    ONE )) === cmp( 0,  1)
        @test @inferred(cmp( ZERO,  (-ONE))) === cmp( 0, -1)
        @test @inferred(cmp(  ONE,   ZERO )) === cmp( 1,  0)
        @test @inferred(cmp(  ONE,    ONE )) === cmp( 1,  1)
        @test @inferred(cmp(  ONE,  (-ONE))) === cmp( 1, -1)
        @test @inferred(cmp((-ONE),  ZERO )) === cmp(-1,  0)
        @test @inferred(cmp((-ONE),   ONE )) === cmp(-1,  1)
        @test @inferred(cmp((-ONE), (-ONE))) === cmp(-1, -1)
    end

    # FIXME n // n needs rem

    values = Number[
        ZERO, -ONE, ONE,
        true, false,
        -5, -2, -1, 0, 1, 2, 7,
        0x00, 0x01, 0x02, 0x7f, 0xff,
        pi,
        0//1, 1//3, -2//7,
        -7.125f0, -1.0f0, -0.0f0, 0.0f0, 1.0f0, 5.75f0,
        -3.5, -1.0, -0.0, 0.0, 1.0, 2.0, 4.25,
        big(-2), big(-1), big(1), big(0), big(3),
        big(-2.25), big(-1.0), big(1.0), big(0.0), big(3.125),
        1 + 2im, 0.0 - 1.0im,
    ]
    @testset "`copysign` with x::$(typeof(x)) = $x" for x in filter(!iscomplex, values)
        if x isa Bool
            # Booleans are non-negative and are converted to `Int` by `copysign`.
            @test same_value_and_type(@inferred(copysign(x, ZERO)),  Int(x))
            @test same_value_and_type(@inferred(copysign(x,  ONE)),  Int(x))
            @test same_value_and_type(@inferred(copysign(x, -ONE)), -Int(x))
        else
            @test same_value_and_type(@inferred(copysign(x, ZERO)), signbit(x) ? -x :  x)
            @test same_value_and_type(@inferred(copysign(x,  ONE)), signbit(x) ? -x :  x)
            @test same_value_and_type(@inferred(copysign(x, -ONE)), signbit(x) ?  x : -x)
        end
    end

    @testset "Multiplication with x::$(typeof(x)) = $x" for x in values
        @test same_value_and_type(@inferred(ZERO*x),   ZERO)
        @test same_value_and_type(@inferred(x*ZERO),   ZERO)
        @test same_value_and_type(@inferred(ONE*x),    x)
        @test same_value_and_type(@inferred(x*ONE),    x)
        @test same_value_and_type(@inferred((-ONE)*x), -x)
        @test same_value_and_type(@inferred(x*(-ONE)), -x)
    end

    @testset "Division with x::$(typeof(x)) = $x" for x in values
        @test same_value_and_type(@inferred(ZERO/x),   (x isa Neutral{0}) ? NaN : ZERO)
        @test same_value_and_type(@inferred(x\ZERO),   ZERO/x)
        @test same_value_and_type(@inferred(x/ZERO),   (x isa Neutral{0}) ? NaN : infinity(x))
        @test same_value_and_type(@inferred(ZERO\x),   x/ZERO)
        @test same_value_and_type(@inferred(ONE/x),    inv(x))
        @test same_value_and_type(@inferred(x\ONE),    ONE/x)
        @test same_value_and_type(@inferred(x/ONE),    x)
        @test same_value_and_type(@inferred(ONE\x),    x/ONE)
        @test same_value_and_type(@inferred((-ONE)/x), -inv(x))
        @test same_value_and_type(@inferred(x\(-ONE)), (-ONE)/x)
        if can_be_truly_negated(x)
            @test same_value_and_type(@inferred(x/(-ONE)), -x)
            @test same_value_and_type(@inferred((-ONE)\x), x/(-ONE))
        else
            @test_throws OverflowError x/(-ONE)
            @test_throws OverflowError (-ONE)\x
        end
    end

    @testset "Rational with x::$(typeof(x)) = $x" for x in filter(x -> x isa Integer, values)
        if x === ZERO
            @test same_value_and_type(@inferred(ZERO // x), NaN)
        else
            @test same_value_and_type(@inferred(ZERO // x), ZERO)
            inf_num = (x isa Bool ? 1 : x < 0 ? -one(x) : one(x))
            inf_den = (x isa Bool ? 0 : zero(x))
            @test same_value_and_type(@inferred(x // ZERO), inf_num // inf_den)
        end

        @test same_value_and_type(@inferred(x // ONE), x)
        @test same_value_and_type(@inferred(ONE // x), one(x) // x)

        if can_be_truly_negated(x)
            @test same_value_and_type(@inferred(x // (-ONE)), -x)
        else
            @test_throws OverflowError x // (-ONE)
        end
        if can_be_truly_negated(one(x))
            @test same_value_and_type(@inferred((-ONE) // x), (-one(x)) // x)
        else
            @test_throws OverflowError (-ONE) // x
        end
    end

    @testset "Addition with x::$(typeof(x)) = $x" for x in values
        @test same_value_and_type(@inferred(ZERO + x),   x)
        @test same_value_and_type(@inferred(x + ZERO),   x)
        @test same_value_and_type(@inferred(ONE + x),    add(ONE, x))
        @test same_value_and_type(@inferred(x + ONE),    add(x, ONE))
        @test same_value_and_type(@inferred((-ONE) + x), add(-ONE, x))
        @test same_value_and_type(@inferred(x + (-ONE)), add(x, -ONE))
    end

    @testset "Subtraction with x::$(typeof(x)) = $x" for x in values
        @test same_value_and_type(@inferred(ZERO - x),   -x)
        @test same_value_and_type(@inferred(x - ZERO),   x)
        @test same_value_and_type(@inferred(ONE - x),    sub(ONE, x))
        @test same_value_and_type(@inferred(x - ONE),    sub(x, ONE))
        @test same_value_and_type(@inferred((-ONE) - x), sub(-ONE, x))
        @test same_value_and_type(@inferred(x - (-ONE)), sub(x, -ONE))
    end

    @testset "Exhaustive addition and subtraction with x::$T" for T in (Int8, UInt8)
        r = typemin(T):typemax(T)
        @test all([ ZERO  + x ===  zero(T)  + x for x in r])
        @test all([  ONE  + x ===   one(T)  + x for x in r])
        @test all([(-ONE) + x === (-one(T)) + x for x in r])
        @test all([x +  ZERO  === x +  zero(T)  for x in r])
        @test all([x +   ONE  === x +   one(T)  for x in r])
        @test all([x + (-ONE) === x + (-one(T)) for x in r])
        @test all([ ZERO  - x ===  zero(T)  - x for x in r])
        @test all([  ONE  - x ===   one(T)  - x for x in r])
        @test all([(-ONE) - x === (-one(T)) - x for x in r])
        @test all([x -  ZERO  === x -  zero(T)  for x in r])
        @test all([x -   ONE  === x -   one(T)  for x in r])
        @test all([x - (-ONE) === x - (-one(T)) for x in r])
    end

    @testset "Exhaustive tests of bitwise OR with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([ ZERO  | x ===   zero(T)  | x for x in r])
        @test all([  ONE  | x ===    one(T)  | x for x in r])
        @test all([(-ONE) | x === (~zero(T)) | x for x in r])
        @test all([x |  ZERO  === x |   zero(T)  for x in r])
        @test all([x |   ONE  === x |    one(T)  for x in r])
        @test all([x | (-ONE) === x | (~zero(T)) for x in r])
    end

    @testset "Exhaustive tests of bitwise AND with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([ ZERO  & x ===   zero(T)  & x for x in r])
        @test all([  ONE  & x ===    one(T)  & x for x in r])
        @test all([(-ONE) & x === (~zero(T)) & x for x in r])
        @test all([x &  ZERO  === x &   zero(T)  for x in r])
        @test all([x &   ONE  === x &    one(T)  for x in r])
        @test all([x & (-ONE) === x & (~zero(T)) for x in r])
    end

    @testset "Exhaustive tests of bitwise XOR with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([xor( ZERO,  x) === xor(  zero(T),  x) for x in r])
        @test all([xor(  ONE,  x) === xor(   one(T),  x) for x in r])
        @test all([xor((-ONE), x) === xor((~zero(T)), x) for x in r])
        @test all([xor(x,  ZERO ) === xor(x,   zero(T) ) for x in r])
        @test all([xor(x,   ONE ) === xor(x,    one(T) ) for x in r])
        @test all([xor(x, (-ONE)) === xor(x, (~zero(T))) for x in r])
    end

    @testset "Exhaustive tests of `<<` with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([ ZERO  << x ===  0 <<  x for x in r])
        @test all([  ONE  << x ===  1 <<  x for x in r])
        @test all([(-ONE) << x === -1 <<  x for x in r])
        @test all([x <<  ZERO  ===  x <<  0 for x in r])
        @test all([x <<   ONE  ===  x <<  1 for x in r])
        @test all([x << (-ONE) ===  x << -1 for x in r])
    end

    @testset "Exhaustive tests of `>>` with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([ ZERO  >> x ===  0 >>  x for x in r])
        @test all([  ONE  >> x ===  1 >>  x for x in r])
        @test all([(-ONE) >> x === -1 >>  x for x in r])
        @test all([x >>  ZERO  ===  x >>  0 for x in r])
        @test all([x >>   ONE  ===  x >>  1 for x in r])
        @test all([x >> (-ONE) ===  x >> -1 for x in r])
    end

    @testset "Exhaustive tests of `>>>` with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([ ZERO  >>> x ===  0 >>>  x for x in r])
        @test all([  ONE  >>> x ===  1 >>>  x for x in r])
        @test all([(-ONE) >>> x === -1 >>>  x for x in r])
        @test all([x >>>  ZERO  ===  x >>>  0 for x in r])
        @test all([x >>>   ONE  ===  x >>>  1 for x in r])
        @test all([x >>> (-ONE) ===  x >>> -1 for x in r])
    end

    @testset "Exhaustive tests of `==` with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([( ZERO  == x) === ( 0 ==  x) for x in r])
        @test all([(  ONE  == x) === ( 1 ==  x) for x in r])
        @test all([((-ONE) == x) === (-1 ==  x) for x in r])
        @test all([(x ==  ZERO ) === ( x ==  0) for x in r])
        @test all([(x ==   ONE ) === ( x ==  1) for x in r])
        @test all([(x == (-ONE)) === ( x == -1) for x in r])
    end

    @testset "Exhaustive tests of `<` with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([( ZERO  < x) === ( 0 <  x) for x in r])
        @test all([(  ONE  < x) === ( 1 <  x) for x in r])
        @test all([((-ONE) < x) === (-1 <  x) for x in r])
        @test all([(x <  ZERO ) === ( x <  0) for x in r])
        @test all([(x <   ONE ) === ( x <  1) for x in r])
        @test all([(x < (-ONE)) === ( x < -1) for x in r])
    end

    @testset "Exhaustive tests of `<=` with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([( ZERO  <= x) === ( 0 <=  x) for x in r])
        @test all([(  ONE  <= x) === ( 1 <=  x) for x in r])
        @test all([((-ONE) <= x) === (-1 <=  x) for x in r])
        @test all([(x <=  ZERO ) === ( x <=  0) for x in r])
        @test all([(x <=   ONE ) === ( x <=  1) for x in r])
        @test all([(x <= (-ONE)) === ( x <= -1) for x in r])
    end

    @testset "Exhaustive tests of `cmp` with x::$T" for T in (Bool, UInt8, Int8)
        r = typemin(T):typemax(T)
        @test all([cmp( ZERO,  x) === cmp( 0,  x) for x in r])
        @test all([cmp(  ONE,  x) === cmp( 1,  x) for x in r])
        @test all([cmp((-ONE), x) === cmp(-1,  x) for x in r])
        @test all([cmp(x,  ZERO ) === cmp( x,  0) for x in r])
        @test all([cmp(x,   ONE ) === cmp( x,  1) for x in r])
        @test all([cmp(x, (-ONE)) === cmp( x, -1) for x in r])
    end

    types = (Bool, Int16, Float32)
    @testset "Broadcasted operations with x::$(typeof(x))" for T in types, x in (zero(T), oneunit(T), rand(T, 3, 4),)
        if x isa AbstractArray
            z = similar(x, typeof(ZERO))
            u = fill!(similar(x), oneunit(eltype(x)))
            r = inv.(x)
        else
            z = ZERO
            u = oneunit(x)
            r = inv(x)
        end

        @test @inferred(x .+ ZERO) === x
        @test @inferred(x .- ZERO) === x
        @test @inferred(x .*  ONE) === x
        @test @inferred(x  *  ONE) === x
        @test @inferred(x ./  ONE) === x
        @test @inferred(x  /  ONE) === x
        @test @inferred(ZERO .+ x) === x
        @test @inferred(ONE  .* x) === x
        @test @inferred(ONE   * x) === x
        @test same_value_and_type(@inferred(ZERO .- x), -x)
        @test same_value_and_type(@inferred(ZERO .* x),  z)
        @test same_value_and_type(@inferred(ZERO  * x),  z)
        @test same_value_and_type(@inferred(x .* ZERO),  z)
        @test same_value_and_type(@inferred(x  * ZERO),  z)
    end

    @testset "Usage examples" begin
        x = [Inf, NaN, -Inf, -NaN]
        @test all(iszero, ZERO .* x)
        y = similar(x)
        @. y = ZERO*x
        @test all(iszero, y)
        copyto!(y, 1:length(y))
        z = similar(y)
        @. z = ONE*y
        @test all(yz -> isequal(yz...), zip(y, z))
        @. z = (-ONE)*y
        @test all(yz -> isequal(yz...), zip(-y, z))
        @. z = 2*y + ZERO*x
        @test all(yz -> isequal(yz...), zip(2y, z))
    end

    @testset "Multipliers" begin
        x = Float32[0,1,2]
        @test @inferred(adapt_multiplier_precision(ZERO, x)) === ZERO
        @test @inferred(adapt_multiplier_precision( ONE, x)) ===  ONE
        @test @inferred(adapt_multiplier_precision(-ONE, x)) === -ONE
        @test @inferred(adapt_multiplier_precision(ZERO, typeof(x))) === ZERO
        @test @inferred(adapt_multiplier_precision( ONE, typeof(x))) ===  ONE
        @test @inferred(adapt_multiplier_precision(-ONE, typeof(x))) === -ONE
        @test @inferred(adapt_multiplier_precision(eltype(x), ZERO)) === ZERO
        @test @inferred(adapt_multiplier_precision(eltype(x),  ONE)) ===  ONE
        @test @inferred(adapt_multiplier_precision(eltype(x), -ONE)) === -ONE
    end

    @testset "Special rules for complexes" begin
        @test Complex(ZERO, ZERO) === complex(ZERO, ZERO) === ZERO + ZERO*im   === ZERO
        @test Complex(ZERO,  ONE) === complex(ZERO,  ONE) === ZERO + ONE*im    === im
        @test Complex(ZERO, -ONE) === complex(ZERO, -ONE) === ZERO - ONE*im    === -im
        @test Complex(ZERO, 2)    === complex(ZERO, 2)    === ZERO + 2im       === 2im
        @test Complex(ZERO, pi)   === complex(ZERO, pi)   === ZERO + pi*im     === complex(false, pi)
        @test Complex(ZERO, 3//2) === complex(ZERO, 3//2) === ZERO + (3//2)*im === complex(false, 3//2)
        @test Complex(ONE,  ZERO) === complex(ONE,  ZERO) === ONE  + ZERO*im   === ONE
        @test Complex(-ONE, ZERO) === complex(-ONE, ZERO) === -ONE + ZERO*im   === -ONE
        @test Complex(pi,   ZERO) === complex(pi,   ZERO) === pi   + ZERO*im   === pi
        @test Complex(3//2, ZERO) === complex(3//2, ZERO) === 3//2 + ZERO*im   === 3//2
    end

    @testset "Dispatch objects" begin
        @test @inferred(Neutrals.dispatch(ZERO)) === ZERO
        @test @inferred(Neutrals.dispatch( ONE)) ===  ONE
        @test @inferred(Neutrals.dispatch(-ONE)) === -ONE
        @test @inferred(Neutrals.dispatch(   π)) === π
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
    end

    @testset "Macros" begin
        ex = @macroexpand Neutrals.@dispatch_on_value β unsafe_xpby!(dst, x, β, y)
        @test ex isa Expr
        @test ex.head == :if
    end

    @testset "Code quality (Aqua.jl)" begin
        Aqua.test_all(Neutrals)
    end

end
