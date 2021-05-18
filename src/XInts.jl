module XInts

export XInt

using Base.GMP: Limb, BITS_PER_LIMB, SLimbMax, ULimbMax, ClongMax, CulongMax, CdoubleMax
import Base.GMP.MPZ
using Base.GC: @preserve
import Base: +, -, *, ^, &, |, ==, /, ~, <<, >>, >>>, <, <=,
             string, widen, hastypemax, tryparse_internal,
             unsafe_trunc, trunc, mod, rem, iseven, isodd, gcd, lcm, xor, div, fld, cld,
             invmod, count_ones, trailing_zeros, trailing_ones, cmp, isqrt,
             flipsign, powermod, gcdx, promote_rule, factorial, binomial

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

promote_rule(::Type{XInt}, ::Type{<:Integer}) = XInt
promote_rule(::Type{XInt}, ::Type{BigInt}) = XInt
promote_rule(::Type{BigInt}, ::Type{XInt}) = XInt

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

# TODO: 3+ args specializations for some ops, like in gmp.jl
# TODO: add efficient sum(arr::AbstractArray{XInt})

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

divrem(x::XInt, y::XInt) = is_short(x, y) ? XInt.(divrem(x.x, y.x)) :
                                            @bigint () x y XInt.(MPZ.tdiv_qr(x, y))

# TODO: remove @bigint when float(::XInt) is implemented
/(x::XInt, y::XInt) = @bigint () x y float(x)/float(y)

invmod(x::XInt, y::XInt) =
    is_short(x, y) ? XInt(invmod(widen(x.x), widen(y.x))) :
                     @bigint () x y XInt(invmod(x, y))

# Basic arithmetic without promotion
+(x::XInt, c::CulongMax) = is_short(x) ? XInt(widen(x.x) + c) :
                                         @bigint () x XInt(MPZ.add_ui(x, c))
+(c::CulongMax, x::XInt) = x + c

-(x::XInt, c::CulongMax) = is_short(x) ? XInt(widen(x.x) - c) :
                                         @bigint () x XInt(MPZ.sub_ui(x, c))

-(c::CulongMax, x::XInt) = is_short(x) ? XInt(c - widen(x.x)) :
                                         @bigint () x XInt(MPZ.ui_sub(c, x))

+(x::XInt, c::ClongMax) = c < 0 ? -(x, -(c % Culong)) : x + convert(Culong, c)
+(c::ClongMax, x::XInt) = c < 0 ? -(x, -(c % Culong)) : x + convert(Culong, c)
-(x::XInt, c::ClongMax) = c < 0 ? +(x, -(c % Culong)) : -(x, convert(Culong, c))
-(c::ClongMax, x::XInt) = c < 0 ? -(x + -(c % Culong)) : -(convert(Culong, c), x)

*(x::XInt, c::CulongMax) = is_short(x) ? XInt(widen(x.x) * c) :
                                         @bigint () x XInt(MPZ.mul_ui(x, c))

*(c::CulongMax, x::XInt) = x * c

*(x::XInt, c::ClongMax) = is_short(x) ? XInt(widen(x.x) * c) :
                                        @bigint () x XInt(MPZ.mul_si(x, c))

*(c::ClongMax, x::XInt) = x * c

# TODO: remove @bigint when float(::XInt) is implemented
/(x::XInt, y::Union{ClongMax,CulongMax}) = @bigint () x float(x)/y
/(x::Union{ClongMax,CulongMax}, y::XInt) = @bigint () y x/float(y)

# unary ops
(-)(x::XInt) = is_short(x) ? XInt(-widen(x.x)) : @bigint () x XInt(MPZ.neg(x))
(~)(x::XInt) = is_short(x) ? XInt(~x.x) : @bigint () x XInt(MPZ.com(x))

<<(x::XInt, c::UInt) = c == 0 ? x : @bigint z x XInt(MPZ.mul_2exp!(z, x, c))
>>(x::XInt, c::UInt) = c == 0 ? x : is_short(x) ? XInt(x.x >> c) :
                                    @bigint z x XInt(MPZ.fdiv_q_2exp!(z, x, c))
>>>(x::XInt, c::UInt) = x >> c

trailing_zeros(x::XInt) =
    if is_short(x)
        iszero(x.x) && throw(DomainError(x)) # InexactError for BigInt
        trailing_zeros(x.x)
    else
        @bigint () x MPZ.scan1(x, 0)
    end

trailing_ones(x::XInt) =
    if is_short(x)
        x.x == -1 && throw(DomainError(x))
        trailing_ones(x.x)
    else
        @bigint () x MPZ.scan0(x, 0)
    end

count_ones(x::XInt) =
    if is_short(x)
        x.x < 0 && throw(DomainError(x))
        count_ones(x.x)
    else
        @bigint () x MPZ.popcount(x)
    end


cmp(x::XInt, y::XInt) = is_short(x, y) ? cmp(x.x, y.x) : @bigint () x y cmp(x, y)
cmp(x::XInt, y::Integer) = is_short(x) ? cmp(x.x, y) : @bigint () x cmp(x, y)
cmp(y::Integer, x::XInt) = -cmp(x, y)
cmp(x::XInt, y::CdoubleMax) = is_short(x) ? cmp(x.x, y) : @bigint () x cmp(x, y)
cmp(y::CdoubleMax, x::XInt) = -cmp(x, y)

<=(x::XInt, y::XInt) = cmp(x,y) <= 0
<=(x::XInt, i::Integer) = cmp(x,i) <= 0
<=(i::Integer, x::XInt) = cmp(x,i) >= 0
<=(x::XInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) <= 0
<=(f::CdoubleMax, x::XInt) = isnan(f) ? false : cmp(x,f) >= 0

<(x::XInt, y::XInt) = cmp(x,y) < 0
<(x::XInt, i::Integer) = cmp(x,i) < 0
<(i::Integer, x::XInt) = cmp(x,i) > 0
<(x::XInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) < 0
<(f::CdoubleMax, x::XInt) = isnan(f) ? false : cmp(x,f) > 0

isqrt(x::XInt) = is_short(x) ? XInt(isqrt(x.x)) : @bigint z x XInt(MPZ.sqrt!(z, x))

^(x::XInt, y::Culong) = @bigint z x XInt(MPZ.pow_ui!(z, x, y))

function xint_pow(x::XInt, y::Integer)
    if y<0; throw(DomainError(y, "`y` cannot be negative.")); end
    @noinline throw1(y) =
        throw(OverflowError("exponent $y is too large and computation will overflow"))
    if x== 1; return x; end
    if x==-1; return isodd(y) ? x : -x; end
    if y>typemax(Culong)
       x==0 && return x

       #At this point, x is not 1, 0 or -1 and it is not possible to use
       #gmpz_pow_ui to compute the answer. Note that the magnitude of the
       #answer is:
       #- at least 2^(2^32-1) ≈ 10^(1.3e9) (if Culong === UInt32).
       #- at least 2^(2^64-1) ≈ 10^(5.5e18) (if Culong === UInt64).
       #
       #Assume that the answer will definitely overflow.

       throw1(y)
    end
    return x^convert(Culong, y)
end

^(x::XInt   , y::XInt   ) = xint_pow(x, y)
^(x::XInt   , y::BigInt ) = xint_pow(x, y)
^(x::BigInt , y::XInt   ) = @bigint () y Base.GMP.bigint_pow(x, y)
^(x::XInt   , y::Bool   ) = y ? x : one(x)
^(x::XInt   , y::Integer) = xint_pow(x, y)
^(x::Integer, y::XInt   ) = xint_pow(XInt(x), y)
^(x::Bool   , y::XInt   ) = Base.power_by_squaring(x, y)

powermod(x::XInt, p::XInt, m::XInt) =
    is_short(x, p) && is_short(m) ? XInt(powermod(x.x, p.x, m.x)) :
                                    @bigint () x p m XInt(powermod(x, p, m))

powermod(x::Integer, p::Integer, m::XInt) = powermod(XInt(x), XInt(p), m)

function gcdx(a::XInt, b::XInt)
    is_short(a, b) &&
        return XInt.(gcdx(widen(a.x), widen(b.x)))
        # widen above necessary at least for (a, b) == (typemin(Int), 0)
    if iszero(b) # shortcut this to ensure consistent results with gcdx(a,b)
        return a < 0 ? (-a,-one(XInt),b) : (a,one(XInt),b)
    end
    g, s, t = XInt.(@bigint (x, y, z) a b MPZ.gcdext!(x, y, z, a, b))
    if t == 0
        # work around a difference in some versions of GMP
        if a == b
            return g, t, s
        elseif abs(a)==abs(b)
            return g, t, -s
        end
    end
    g, s, t
end


flipsign(x::XInt, y::Integer) = signbit(y) ? -x : x
flipsign(x::XInt, y::XInt)  = signbit(y) ? -x : x

factorial(x::XInt) = signbit(x) ? throw(DomainError(x)) :
                                  @bigint z x XInt(MPZ.fac_ui!(z, x))

binomial(x::XInt, k::UInt) = @bigint z x XInt(MPZ.bin_ui!(z, x, k))
binomial(x::XInt, k::Integer) = k < 0 ? XInt(0) : binomial(x, UInt(k))

end # module
