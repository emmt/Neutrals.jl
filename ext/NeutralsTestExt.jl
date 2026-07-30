module NeutralsTestExt

if isdefined(Base, :get_extension)
    using Neutrals, Test
else
    using ..Neutrals, ..Test
end

import .Neutrals: test_binary_operations

function test_binary_operations(vals::Number...)
    for x in vals
        test_binary_operations(x)
    end
end

function test_binary_operations(vals::Union{Tuple{Number,Vararg{Number}},
                                            AbstractArray{<:Number}})
    for x in vals
        test_binary_operations(x)
    end
end

function test_binary_operations(x::Number)
    # Check commutativity or similar properties of some operations.
    for y ∈ instances(Neutral)
        # Commutative operations.
        ops = [:(+), :(+), :(==), :isequal]
        x isa Integer && push!(ops, :(|), :(&), :xor) # bitwise operations
        for f in ops
            @eval begin
                @test @inferred($f($x, $y)) === @inferred($f($y, $x))
            end
        end
        # Anti-commutative operations.
        if !(x isa Complex)
            for f in [:cmp,]
                @eval begin
                    @test @inferred($f($x, $y)) === -@inferred($f($y, $x))
                end
            end
        end
        # x\y is equivalent to y/x.
        @eval begin
            @test @inferred($x \ $y) === @inferred($y / $x)
            if iszero($y) #= FIXME && real_type($x) < Integer =#
                @test_throws DivideError $y \ $x
            else
                @test @inferred($y \ $x) === @inferred($x / $y)
            end
        end
    end

    eq = x isa Union{BigInt, BigFloat} ? :(≙) : :(===)

    @eval begin
        @test ===(@inferred($x +  ZERO ), $x)
        @test $eq(@inferred($x +   ONE ), $x + one($x))
        @test $eq(@inferred($x + (-ONE)), $x - one($x))

        @test ===(@inferred($x -  ZERO ), $x)
        @test $eq(@inferred($x -   ONE ), $x - one($x))
        @test $eq(@inferred($x - (-ONE)), $x + one($x))

        @test $eq(@inferred( ZERO  - $x), -$x)
        @test $eq(@inferred(  ONE  - $x), one($x) - $x)
        @test $eq(@inferred((-ONE) - $x), -one($x) - $x)

        @test $eq(@inferred( ZERO  * $x), ZERO) # FIXME
        @test ===(@inferred(  ONE  * $x), $x)
        @test $eq(@inferred((-ONE) * $x), -$x)
        #
        @test $eq(@inferred( ZERO  / $x), ZERO) # FIXME
        @test $eq(@inferred(  ONE  / $x), inv($x))
        @test $eq(@inferred((-ONE) / $x), -inv($x))

        @test_throws DivideError $x / ZERO
        # FIXME if real_type($x) <: Integer
        # FIXME     @test_throws DivideError $x / ZERO
        # FIXME else
        # FIXME     @test $eq($x / ZERO, $x / zero($x)) # FIXME 0.0/ZERO -> +Inf, not NaN
        # FIXME end
        @test $eq(@inferred($x /   ONE ), $x)
        @test $eq(@inferred($x / (-ONE)), -$x)

        @test $eq(@inferred($x ^ ZERO ), one($x))
        @test $eq(@inferred($x ^  ONE ), $x)
        @test $eq(@inferred($x ^(-ONE)), inv($x))
    end
end

end # module
