module NeutralsUnitfulExt

if isdefined(Base, :get_extension)
    using Neutrals, Unitful
    using Unitful: AbstractQuantity, Quantity, NoDims, unit, ustrip
else
    using ..Neutrals, ..Unitful
    using ..Unitful: AbstractQuantity, Quantity, NoDims, unit, ustrip
end

# Preserve units in multiplication and division.
Neutrals.impl_mul(x::Neutral{0}, y::AbstractQuantity) = x*unit(y)

Neutrals.impl_div(x::Neutral{0}, y::AbstractQuantity) = x/unit(y)

Neutrals.impl_mul(x::Neutral{0}, y::AbstractArray{<:AbstractQuantity}) =
    similar(y, typeof(x*unit(eltype(y))))

Neutrals.impl_div(x::Neutral, y::AbstractArray{<:AbstractQuantity{Neutral{0}}}) =
    throw(DivideError())
Neutrals.impl_div(x::Neutral, y::AbstractArray{<:AbstractQuantity}) =
    _impl_div(x, y) # to dispatch on x

Neutrals._impl_div(x::Neutral{0}, y::AbstractArray{<:AbstractQuantity}) =
    similar(y, typeof(x/unit(eltype(y))))

Neutrals.is_dimensionless(::Type{<:AbstractQuantity}) = false
Neutrals.is_dimensionless(::Type{<:AbstractQuantity{<:Any,NoDims}}) = true

# Override base methods to call corresponding implementation for binary operations
# involving a quantity and a neutral number.
for (f, (g, w)) in (:(+)   => (:impl_add,    3),
                    :(-)   => (:impl_sub,    3),
                    :(*)   => (:impl_mul,    3),
                    :(/)   => (:impl_div,    3),
                    :(^)   => (:impl_pow,    2),
                    :div   => (:impl_trd,    3),
                    :rem   => (:impl_rem,    3),
                    :mod   => (:impl_mod,    3),
                    :(==)  => (:impl_eq,     3),
                    :(<)   => (:impl_lt,     3),
                    :(<=)  => (:impl_le,     3),
                    :cmp   => (:impl_cmp,    3),
                    :(|)   => (:impl_or,     3),
                    :(&)   => (:impl_and,    3),
                    :xor   => (:impl_xor,    3),
                    :(<<)  => (:impl_lshft,  2),
                    :(>>)  => (:impl_rshft,  2),
                    :(>>>) => (:impl_urshft, 2))
    if (w & 1) != 0
        @eval Base.$f(x::Neutral, y::AbstractQuantity) = Neutrals.$g(x, y)
    end
    if (w & 2) != 0
        @eval Base.$f(x::AbstractQuantity, y::Neutral) = Neutrals.$g(x, y)
    end
end

end # module
