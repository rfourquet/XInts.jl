module XInts

export XInt

using Base.GMP: Limb, BITS_PER_LIMB, SLimbMax, ULimbMax, ClongMax, CulongMax, CdoubleMax
import Base.GMP: isneg, ispos
import Base.GMP.MPZ
import Base.MPFR
using Base.GC: @preserve
import Base: +, -, *, ^, &, |, ==, /, ~, <<, >>, >>>, <, <=,
             string, widen, hastypemax, tryparse_internal,
             unsafe_trunc, trunc, mod, rem, iseven, isodd, gcd, lcm, xor, div, fld, cld,
             invmod, count_ones, trailing_zeros, trailing_ones, cmp, isqrt,
             flipsign, powermod, gcdx, promote_rule, factorial, binomial,
             digits!, ndigits0zpb, signbit, sign, iszero, isone,
             AbstractFloat, BigFloat, float, _prevpow2, _nextpow2,
             hash, hash_integer


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
    const SLimb = Int32
    const SLimbW = Int64
elseif BITS_PER_LIMB == 64
    const SLimb = Int64
    const SLimbW = Int128
else
    error()
end

const slimbmin = typemin(SLimb)
const slimbmax = typemax(SLimb)
# when there is only one limb in a vector, this limb must always be >= limb1min
# only XInt(slimbmin) can have two different representations, as a direct integer
# or with a length-1 vector with value limb1min
const limb1min = slimbmin % Limb # typically 0x8000000000000000

struct XInt <: Signed
    x::SLimb # immediate integer or sign+length
    v::Union{Nothing,Vector{Limb}}

    XInt(x::SLimb) = new(x, nothing)

    global function _XInt(x::SLimb, v::Vector{Limb}, normalize::Bool=false)
        if normalize
            # we still assume length(v) == abs(x); normalize here means to not store
            # a too small integer in a vector representation
            xl = abs(x)
            if xl <= 1
                if xl == 0
                    return new(SLimb(0), nothing)
                else # xl == 1
                    limb = @inbounds v[1]
                    limb < limb1min &&
                        return new(flipsign(limb % SLimb, x), nothing)
                end
            end
        end
        new(x, v)
    end
end

is_short(x::XInt) = x.v === nothing
is_short(x::XInt, y::XInt) = x.v === nothing === y.v

include("MPN.jl")
include("mutants.jl")

MPN.ptr(x::XInt) = pointer(x.v::Vector{Limb})
MPN.len(x::XInt) = abs(x.x) % MPN.Size

function XInt(z::BigInt)
    len = abs(z.size)
    if len == 0
        XInt(zero(SLimb))
    elseif len == 1 && (x = unsafe_load(z.d)) <= slimbmax
        XInt(flipsign(x % SLimb, z.size))
    else
        x = _XInt(z.size % SLimb, Vector{Limb}(undef, len))
        @preserve x z unsafe_copyto!(pointer(x.v), z.d, len)
        x
    end
end

XInt(z::SLimbMax) = XInt(z % SLimb)

XInt(z::Limb) = z <= slimbmax ? XInt(z % SLimb) :
                                _XInt(one(SLimb), Limb[z])

XInt(z::SLimbW) = XInt!(nothing, z)

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

BigInt(x::XInt) = is_short(x) ? BigInt(x.x) : @bigint () x MPZ.set(x)

Base.show(io::IO, x::XInt) = print(io, string(x))

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
isneg(x::XInt) = x.x < 0
signbit(x::XInt) = x.x < 0
sign(x::XInt) = XInt(sign(x.x))
iszero(x::XInt) = iszero(x.x)
isone(x::XInt) = is_short(x) ? isone(x.x) : isone(@inbounds x.v[1])
# TODO: remove is_short check when we guarantee that short integers are always stored in x.x

function (::Type{T})(x::XInt) where T<:Base.BitSigned
    is_short(x) && return T(x.x)
    n = abs(x.x)
    if sizeof(T) < sizeof(Limb)
        # @assert SLimb == typeof(Signed(one(Limb)))
        convert(T, convert(SLimb, x))
    else
        0 <= n <= cld(sizeof(T), sizeof(Limb)) || throw(InexactError(nameof(T), T, x))
        y = x % T
        ispos(x) ⊻ (y > 0) && throw(InexactError(nameof(T), T, x)) # catch overflow
        y
    end
end

Float64(x::XInt, ::RoundingMode{:ToZero}) =
    is_short(x) ? Float64(x.x, RoundToZero) : @bigint () x MPZ.get_d(x)


function (::Type{T})(x::XInt, ::RoundingMode{:ToZero}) where T<:Union{Float16,Float32}
    T(Float64(x, RoundToZero), RoundToZero)
end

function (::Type{T})(n::XInt, ::RoundingMode{:Down}) where T<:CdoubleMax
    x = T(n, RoundToZero)
    x > n ? prevfloat(x) : x
end

function (::Type{T})(n::XInt, ::RoundingMode{:Up}) where T<:CdoubleMax
    x = T(n, RoundToZero)
    x < n ? nextfloat(x) : x
end

for T = [Float16, Float32, Float64]
    @eval (::Type{$T})(x::XInt, r::RoundingMode{:Nearest}=RoundNearest) =
        is_short(x) ? $T(x.x, r) : @bigint () x $T(x, r)
end

AbstractFloat(x::XInt) = BigFloat(x)

BigFloat(x::XInt, r::MPFR.MPFRRoundingMode=MPFR.ROUNDING_MODE[];
         precision::Integer=MPFR.DEFAULT_PRECISION[]) =
             is_short(x) ? BigFloat(x.x, r; precision=precision) :
                           @bigint () x BigFloat(x, r; precision=precision)

float(::Type{XInt}) = BigFloat

# Binary ops
for (fJ, fC) in ((:-,:sub), (:*, :mul),
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

+(x::XInt, y::XInt) = add!(nothing, x, y)

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

function ==(x::XInt, y::XInt)
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

==(x::XInt, f::CdoubleMax) = isnan(f) ? false : cmp(x, f) == 0
==(f::CdoubleMax, x::XInt) = isnan(f) ? false : cmp(x, f) == 0

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

function digits!(a::AbstractVector{T}, n::XInt; base::Integer = 10) where {T<:Integer}
    if 2 ≤ base ≤ 62
        s = codeunits(string(n; base=base))
        i, j = firstindex(a)-1, length(s)+1
        lasti = min(lastindex(a), firstindex(a) + length(s)-1 - isneg(n))
        while i < lasti
            # base ≤ 36: 0-9, plus a-z for 10-35
            # base > 36: 0-9, plus A-Z for 10-35 and a-z for 36..61
            x = s[j -= 1]
            a[i += 1] = base ≤ 36 ? (x>0x39 ? x-0x57 : x-0x30) : (x>0x39 ? (x>0x60 ? x-0x3d : x-0x37) : x-0x30)
        end
        lasti = lastindex(a)
        while i < lasti; a[i+=1] = zero(T); end
        return isneg(n) ? map!(-,a,a) : a
    end
    return invoke(digits!, Tuple{typeof(a), Integer}, a, n; base=base) # slow generic fallback
end

ndigits0zpb(x::XInt, b::Integer) = is_short(x) ? ndigits0zpb(x.x, b) :
                                                 @bigint () x ndigits0zpb(x, b)

function _prevpow2(x::XInt)
    if is_short(x)
        XInt(_prevpow2(x.x))
    else
        len = abs(x.x)
        @assert length(x.v) == len
        high = @inbounds x.v[end]
        @assert !iszero(high) # like for BigInt/mpz_t
        shift = BITS_PER_LIMB - leading_zeros(high) - 1
        v = fill(zero(Limb), len)
        @inbounds v[end] = one(Limb) << shift
        _XInt(x.x, v)
    end
end

function _nextpow2(x::XInt)
    if is_short(x)
        y = _nextpow2(x.x)
        if sign(x) != sign(y)
            @assert y == typemin(Int)
            _XInt(1, Limb[typemin(Int) % Limb])
        else
            XInt(y)
        end
    else
        len = abs(x.x)
        @assert length(x.v) == len
        popcount = GC.@preserve x MPZ.mpn_popcount(pointer(x.v), len)
        if popcount <= 1
            @assert popcount == 1
            return x
        end
        high = @inbounds x.v[end]
        @assert !iszero(high) # like for BigInt/mpz_t
        shift = (BITS_PER_LIMB - leading_zeros(high)) & (BITS_PER_LIMB-1)
        newlen = len + iszero(shift)
        v = fill(zero(Limb), newlen)
        @inbounds v[end] = one(Limb) << shift
        _XInt(flipsign(newlen, x.x), v)
    end
end


Base.checked_abs(x::XInt) = abs(x)
Base.checked_neg(x::XInt) = -x
Base.checked_add(a::XInt, b::XInt) = a + b
Base.checked_sub(a::XInt, b::XInt) = a - b
Base.checked_mul(a::XInt, b::XInt) = a * b
Base.checked_div(a::XInt, b::XInt) = div(a, b)
Base.checked_rem(a::XInt, b::XInt) = rem(a, b)
Base.checked_fld(a::XInt, b::XInt) = fld(a, b)
Base.checked_mod(a::XInt, b::XInt) = mod(a, b)
Base.checked_cld(a::XInt, b::XInt) = cld(a, b)
Base.add_with_overflow(a::XInt, b::XInt) = a + b, false
Base.sub_with_overflow(a::XInt, b::XInt) = a - b, false
Base.mul_with_overflow(a::XInt, b::XInt) = a * b, false


_copy(x::XInt) = is_short(x) ? x : _XInt(x.x, copy(x.v))

Base.deepcopy_internal(x::XInt, d::IdDict) = get!(() -> _copy(x), d, x)

if Limb === UInt
    using Base: hash_uint

    function hash_integer(x::XInt, h::UInt)
        is_short(x) && return hash_integer(x.x, h)
        sz = x.x
        xv = x.v
        b = @inbounds xv[1]
        h ⊻= hash_uint(ifelse(sz < 0, -b, b) ⊻ h)
        for k = 2:abs(sz)
            h ⊻= hash_uint(@inbounds xv[k] ⊻ h)
        end
        h
    end

    _divLimb(n) = UInt === UInt64 ? n >>> 6 : n >>> 5
    _modLimb(n) = UInt === UInt64 ? n & 63 : n & 31

    function hash(x::XInt, h::UInt)
        GC.@preserve x begin
            is_short(x) && return hash(x.x, h)
            sz = x.x
            xv = x.v
            if sz == 1
                return hash(@inbounds(xv[1]), h)
            elseif sz == -1
                limb = @inbounds xv[1]
                limb <= typemin(Int) % UInt && return hash(-(limb % Int), h)
            end
            pow = trailing_zeros(x)
            nd = Base.ndigits0z(x, 2)
            idx = _divLimb(pow) + 1
            shift = _modLimb(pow) % UInt
            upshift = BITS_PER_LIMB - shift
            asz = abs(sz)
            if shift == 0
                limb = @inbounds xv[idx]
            else
                limb1 = @inbounds xv[idx]
                limb2 = idx < asz ? @inbounds(xv[idx+1]) : UInt(0)
                limb = limb2 << upshift | limb1 >> shift
            end
            if nd <= 1024 && nd - pow <= 53
                return hash(ldexp(flipsign(Float64(limb), sz), pow), h)
            end
            h = hash_integer(1, h)
            h = hash_integer(pow, h)
            h ⊻= hash_uint(flipsign(limb, sz) ⊻ h)
            for idx = idx+1:asz
                if shift == 0
                    limb = @inbounds xv[idx]
                else
                    limb1 = limb2
                    if idx == asz
                        limb = limb1 >> shift
                        limb == 0 && break # don't hash leading zeros
                    else
                        limb2 = @inbounds xv[idx+1]
                        limb = limb2 << upshift | limb1 >> shift
                    end
                end
                h ⊻= hash_uint(limb ⊻ h)
            end
            return h
        end
    end
end

end # module
