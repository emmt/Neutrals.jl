module NeutralsUnitfulExt

if isdefined(Base, :get_extension)
    using Neutrals, Unitful
else
    using ..Neutrals, ..Unitful
end

using .Unitful: AbstractQuantity, DimensionlessQuantity, Quantity, NoDims, unit, ustrip

Neutrals.impl_unit(::Type{<:AbstractQuantity{T,D,U}}) where {T,D,U} = U()

Neutrals.impl_ustrip(x::AbstractQuantity) = ustrip(x)
Neutrals.impl_ustrip(::Type{<:AbstractQuantity{T,D,U}}) where {T,D,U} = T

Neutrals.is_dimensionless(::Type{<:AbstractQuantity}) = false
Neutrals.is_dimensionless(::Type{<:DimensionlessQuantity}) = true

#Neutrals.impl_div(::Val{1}, x::Neutral, y::AbstractArray{<:AbstractQuantity{<:Neutral{0}}}) =
#    throw(DivideError()) # FIXME not needed

# Override base methods to call corresponding implementation for binary operations
# involving a quantity and a neutral number.
for (f, g) in [:(+)     => :impl_add,
               :(-)     => :impl_sub,
               :(*)     => :impl_mul,
               :(/)     => :impl_div,
               :(^)     => :impl_pow,
               :div     => :impl_tdv,
               :rem     => :impl_rem,
               :mod     => :impl_mod,
               :(==)    => :impl_eq,
               :(<)     => :impl_lt,
               :(<=)    => :impl_le,
               :isequal => :impl_isequal,
               :isless  => :impl_isless,
               :cmp     => :impl_cmp,
               :(|)     => :impl_or,
               :(&)     => :impl_and,
               :xor     => :impl_xor,
               :(<<)    => :impl_lshft,
               :(>>)    => :impl_rshft,
               :(>>>)   => :impl_urshft,]
    @eval begin
        Base.$f(x::Neutral, y::AbstractQuantity) = Neutrals.$g(x, y)
        Base.$f(x::AbstractQuantity, y::Neutral) = Neutrals.$g(x, y)
    end
end

end # module
