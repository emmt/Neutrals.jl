module NeutralsUnitfulExt

if isdefined(Base, :get_extension)
    using Neutrals, Unitful
else
    using ..Neutrals, ..Unitful
end

using .Neutrals: is_dimensionless
using .Unitful: AbstractQuantity, Quantity, NoDims, unit, ustrip

# Preserve units in multiplication and division.
Neutrals.impl_mul(::Val{1}, x::Neutral{0}, y::AbstractQuantity) = x*unit(y)

Neutrals.impl_div(::Val{1}, x::Neutral{0}, y::AbstractQuantity) = x/unit(y)

Neutrals.impl_mul(::Val{1}, x::Neutral{0}, y::AbstractArray{<:AbstractQuantity}) =
    similar(y, typeof(x*unit(eltype(y))))

Neutrals.impl_div(::Val{1}, x::Neutral, y::AbstractArray{<:AbstractQuantity{<:Neutral{0}}}) =
    throw(DivideError())
Neutrals.impl_div(::Val{1}, x::Neutral, y::AbstractArray{<:AbstractQuantity}) =
    Neutrals._impl_div(x, y) # to dispatch on x
#
#Neutrals._impl_div(x::Neutral{0}, y::AbstractArray{<:AbstractQuantity}) =
#    similar(y, typeof(x/unit(eltype(y))))

Neutrals.is_dimensionless(::Type{<:AbstractQuantity}) = false
Neutrals.is_dimensionless(::Type{<:AbstractQuantity{<:Any,NoDims}}) = true

# Override base methods to call corresponding implementation for binary operations
# involving a quantity and a neutral number.
for (f, (g, w)) in (:(+)   => (:impl_add,    6),
                    :(-)   => (:impl_sub,    3),
                    :(*)   => (:impl_mul,    5),
                    :(/)   => (:impl_div,    3),
                    :(^)   => (:impl_pow,    2),
                    :div   => (:impl_tdv,    3),
                    :rem   => (:impl_rem,    3),
                    :mod   => (:impl_mod,    3),
                    :(==)  => (:impl_eq,     6),
                    :(<)   => (:impl_lt,     3),
                    :(<=)  => (:impl_le,     3),
                    :cmp   => (:impl_cmp,    3),
                    :(|)   => (:impl_or,     6),
                    :(&)   => (:impl_and,    6),
                    :xor   => (:impl_xor,    6),
                    :(<<)  => (:impl_lshft,  2),
                    :(>>)  => (:impl_rshft,  2),
                    :(>>>) => (:impl_urshft, 2))
    if (w & 1) == 1
        # Implementation exists when 1st operand is a neutral number.
        @eval Base.$f(x::Neutral, y::AbstractQuantity) = Neutrals.$g($(Val(1)), x, y)
    elseif w == 6
        # Operation is commutative and implementation exists when 2nd operand is a
        # neutral number.
        @eval Base.$f(x::Neutral, y::AbstractQuantity) = Neutrals.$g($(Val(2)), y, x)
    end
    if (w & 2) == 2
        # Implementation exists when 2nd operand is a neutral number.
        @eval Base.$f(x::AbstractQuantity, y::Neutral) = Neutrals.$g($(Val(2)), x, y)
    elseif w == 5
        # Operation is commutative and implementation exists when 1st operand is a
        # neutral number.
        @eval Base.$f(x::AbstractQuantity, y::Neutral) = Neutrals.$g($(Val(1)), y, x)
    end
end

end # module
