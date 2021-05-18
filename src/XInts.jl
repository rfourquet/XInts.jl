module XInts

export XInt

using Base.GMP: Limb, BITS_PER_LIMB, SLimbMax, ULimbMax
import Base.GMP.MPZ
using Base.GC: @preserve
import Base: +, -, *, &, |, ==, /, string, widen, hastypemax, tryparse_internal,
             unsafe_trunc, trunc, mod, rem, iseven, isodd, gcd, lcm, xor, div, fld, cld

mutable struct Wrap
    b::BigInt
    d::Ptr{Limb}

    function Wrap(isoutput::Bool=false)
        b = BigInt()
        @assert b.alloc == 1
        @assert b.size == 0
        wrap = new(b, b.d)
        if !isoutput
            # init! was called
            finalizer(wrap) do wrap
                wrap.b.d = wrap.d
                wrap.b.alloc = 1
                wrap.b.size = 0
            end
        end
        wrap
    end
end

if BITS_PER_LIMB == 32
    const Short = Int32
    const ShortW = Int64
elseif BITS_PER_LIMB == 64
    const Short = Int64
    const ShortW = Int128
else
    error()
end

const shortmin = typemin(Short)
const shortmax = typemax(Short)

struct XInt <: Signed
    x::Short # immediate integer or sign+length
    v::Union{Nothing,Vector{Limb}}

    XInt(x::Short) = new(x, nothing)
    XInt(x::Short, v::Vector{Limb}) = new(x, v)
end

is_short(x::XInt) = x.v === nothing
is_short(x::XInt, y::XInt) = x.v === nothing === y.v

function XInt(z::BigInt)
    len = abs(z.size)
    if len == 0
        XInt(zero(Short))
    elseif len == 1 && (x = unsafe_load(z.d)) <= shortmax
        XInt(flipsign(x % Short, z.size))
    else
        x = XInt(z.size % Short, Vector{Limb}(undef, len))
        @preserve x z unsafe_copyto!(pointer(x.v), z.d, len)
        x
    end
end

XInt(z::SLimbMax) = XInt(z % Short)

XInt(z::Limb) = z <= shortmax ? XInt(z % Short) :
                                XInt(one(Short), Limb[z])

XInt(z::ShortW) =
    if shortmin <= z <= shortmax
        XInt(z % Short)
    else
        zz = abs(z)
        z1 = zz % Limb
        z2 = (zz >>> BITS_PER_LIMB) % Limb
        iszero(z2) ?
            XInt(sign(z) % Short, [z1]) :
            XInt(flipsign(Short(2), z), [z1, z2])
    end

XInt(z::Integer) = XInt(BigInt(z)) # TODO: copy over the implementation from gmp.jl

XInt(x::XInt) = x

function XInt(x::Float64)
    isinteger(x) || throw(InexactError(:XInt, XInt, x))
    unsafe_trunc(XInt, x)
end

# no Union, to disambiguate
XInt(x::Float16) = XInt(Float64(x))
XInt(x::Float32) = XInt(Float64(x))

function init!(z::Wrap, x::XInt)
    b = z.b
    if is_short(x)
        b.alloc = 1
        b.size = sign(x.x)
        b.d = z.d
        unsafe_store!(z.d, abs(x.x) % Limb)
    else
        len = x.x
        b.alloc = abs(len)
        b.size = len
        b.d = pointer(x.v)
    end
    z.b::BigInt
end

struct Wraps
    # read-write temporary storage (output arguments)
    U::Wrap
    V::Wrap
    W::Wrap
    # read-only shallow wrappers of BigInt objects ("const" arguments in libgmp)
    X::Wrap
    Y::Wrap
    Z::Wrap

    Wraps() = new(Wrap(true), Wrap(true), Wrap(true), Wrap(), Wrap(), Wrap())
end

const tWraps = Wraps[]

function __init__()
    copy!(tWraps, [Wraps() for _=1:Threads.nthreads()])
end

macro bigint(args...)
    @assert length(args) >= 2
    out = args[1]
    xs = esc.(args[2:end-1])
    body = args[end]

    lets = :(let
                 $(esc(body))
             end)
    vars = lets.args[1].args

    @gensym mpzs
    push!(vars, :($(esc(mpzs)) = tWraps[Threads.threadid()]))
    if !(out isa Expr)
        out = Expr(:tuple, out)
    end
    for (i, outi) in enumerate(out.args)
        push!(vars, :($(esc(outi)) = getfield($(esc(mpzs)), $i).b))
    end
    for (i, xi) in enumerate(xs)
        push!(vars, :($xi = init!(getfield($(esc(mpzs)), $i+3), $xi)))
    end
    Expr(:gc_preserve, lets, xs...)
end


Base.show(io::IO, x::XInt) = @bigint () x show(io, x)

function Base.:(==)(x::XInt, y::XInt)
    if is_short(x, y)
        x.x == y.x
    else
        @bigint () x y x == y
    end
end

==(x::XInt, y::Integer) =
    if is_short(x)
        x.x == y
    else
        @bigint () x x == y
    end

==(x::Integer, y::XInt) = y == x

# disambiguation
==(x::XInt, y::BigInt) = invoke(==, Tuple{XInt, Integer}, x, y)
==(x::BigInt, y::XInt) = y == x

string(n::XInt; base::Integer = 10, pad::Integer = 1) =
    @bigint () n string(n; base=base, pad=pad)

widen(::Type{XInt}) = XInt

hastypemax(::Type{XInt}) = false

tryparse_internal(::Type{XInt}, s::AbstractString, startpos::Int, endpos::Int,
                  base_::Integer, raise::Bool) =
                      XInt(tryparse_internal(BigInt, s, startpos, endpos, base_, raise))

unsafe_trunc(::Type{XInt}, x::Union{Float32,Float64}) = XInt(unsafe_trunc(BigInt, x))

function trunc(::Type{XInt}, x::Union{Float32,Float64})
    isfinite(x) || throw(InexactError(:trunc, XInt, x))
    unsafe_trunc(XInt, x)
end


rem(x::XInt, ::Type{Bool}) =
    is_short(x) ? x.x % Bool :
                  (@inbounds x.v[1]) % Bool

rem(x::XInt, ::Type{T}) where T<:Union{SLimbMax,ULimbMax} =
    is_short(x) ? x.x % T : flipsign((@inbounds x.v[1] % T), x.x)

# TODO: extend to "AbstractBitInteger", when available in Base
function rem(x::XInt, ::Type{T}) where T<:Union{Base.BitUnsigned,Base.BitSigned}
    is_short(x) && return x.x % T
    u = zero(T)
    # TODO: this is missing an optimization that BigInt has; it would be faster here
    # to have a chain of if/elseif based on the value of the min below
    for l = 1:min(abs(x.x), cld(sizeof(T), sizeof(Limb)))
        u += (@inbounds x.v[l] % T) << ((sizeof(Limb)<<3)*(l-1))
    end
    flipsign(u, x.x)
end

rem(x::Integer, ::Type{XInt}) = XInt(x)

isodd(x::XInt) = is_short(x) ? isodd(x.x) : isodd(@inbounds x.v[1])
iseven(x::XInt) = !isodd(x)

function (::Type{T})(x::XInt) where T<:Base.BitUnsigned
    if is_short(x)
        convert(T, x.x)
    elseif sizeof(T) < sizeof(Limb)
        convert(T, convert(Limb, x))
    else
        0 <= x.x <= cld(sizeof(T), sizeof(Limb)) || throw(InexactError(nameof(T), T, x))
        x % T
    end
end

ispos(x::XInt) = x.x > 0

function (::Type{T})(x::XInt) where T<:Base.BitSigned
    is_short(x) && return T(x.x)
    n = abs(x.x)
    if sizeof(T) < sizeof(Limb)
        # @assert Short == typeof(Signed(one(Limb)))
        convert(T, convert(Short, x))
    else
        0 <= n <= cld(sizeof(T), sizeof(Limb)) || throw(InexactError(nameof(T), T, x))
        y = x % T
        ispos(x) ⊻ (y > 0) && throw(InexactError(nameof(T), T, x)) # catch overflow
        y
    end
end


# Binary ops
for (fJ, fC) in ((:+, :add), (:-,:sub), (:*, :mul),
                 (:mod, :fdiv_r), (:rem, :tdiv_r),
                 (:gcd, :gcd), (:lcm, :lcm),
                 (:&, :and), (:|, :ior), (:xor, :xor))
    @eval begin
        ($fJ)(x::XInt, y::XInt) =
            is_short(x, y) ? XInt(($fJ)(widen(x.x), widen(y.x))) :
                             @bigint () x y XInt(MPZ.$fC(x, y))
    end
end

for (r, f) in ((RoundToZero, :tdiv_q),
               (RoundDown, :fdiv_q),
               (RoundUp, :cdiv_q))
    @eval div(x::XInt, y::XInt, ::typeof($r)) =
        is_short(x, y) ? XInt(div(widen(x.x), widen(y.x), $r)) :
                         @bigint () x y XInt(MPZ.$f(x, y))
end

# For compat only. Remove in 2.0.
div(x::XInt, y::XInt) = div(x, y, RoundToZero)
fld(x::XInt, y::XInt) = div(x, y, RoundDown)
cld(x::XInt, y::XInt) = div(x, y, RoundUp)

# TODO: remove @bigint when float(::XInt) is implemented
/(x::XInt, y::XInt) = @bigint () x y float(x)/float(y)


end # module
