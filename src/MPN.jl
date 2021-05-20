module MPN

using Base.GC: @preserve
using Base.GMP: Limb # mp_limb_t
const PLimb = Ptr{Limb}
const Size = Clong # mp_size_t

len(p::Pair) = p[2]
ptr(p::Pair) = ptr(p[1])
ptr(p::Ptr) = p
ptr(p::Array) = pointer(p)

#mp_limb_t mpn_add_1 (mp_limb_t *rp, const mp_limb_t *s1p, mp_size_t n, mp_limb_t s2limb)

add_1(rp, s1, s2) = @preserve rp s1 ccall((:__gmpn_add_1, :libgmp), Limb,
                                          (PLimb, PLimb, Size, Limb),
                                          ptr(rp), ptr(s1), len(s1), s2)

add(rp, s1, s2) = @preserve rp s1 s2 ccall((:__gmpn_add, :libgmp), Limb,
                                           (PLimb, PLimb, Size, PLimb, Size),
                                           ptr(rp), ptr(s1), len(s1), ptr(s2), len(s2))

sub_1(rp, s1, s2) = @preserve rp s1 ccall((:__gmpn_sub_1, :libgmp), Limb,
                                          (PLimb, PLimb, Size, Limb),
                                          ptr(rp), ptr(s1), len(s1), s2)

sub(rp, s1, s2) = @preserve rp s1 s2 ccall((:__gmpn_sub, :libgmp), Limb,
                                           (PLimb, PLimb, Size, PLimb, Size),
                                           ptr(rp), ptr(s1), len(s1), ptr(s2), len(s2))

sub_n(rp, s1, s2, n) = @preserve rp s1 s2 ccall((:__gmpn_sub_n, :libgmp), Limb,
                                                (PLimb, PLimb, PLimb, Size),
                                                ptr(rp), ptr(s1), ptr(s2), n)

cmp(s1, s2) = @preserve s1 s2 ccall((:__gmpn_cmp, :libgmp), Cint,
                                    (Ptr{Limb}, Ptr{Limb}, Clong),
                                    ptr(s1), ptr(s2), len(s1))

end # MPN
