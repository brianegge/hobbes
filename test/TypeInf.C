
#include "test.H"
#include <hobbes/hobbes.H>
#include <hobbes/util/codec.H>
#include <hobbes/util/stream.H>
#include <cstring>
#include <memory>
#include <limits>
#include <sstream>
#include <vector>
#include <functional>

using namespace hobbes;

TEST(TypeInf, Unification) {
  MonoTypeUnifier u(std::make_shared<TEnv>());

  // test unification and substitution between recursive types
  MonoTypePtr t0(Recursive::make("x", sumtype(primty("unit"), tuplety(list(tvar("a"), tvar("x"))))));
  MonoTypePtr t1(Recursive::make("x", sumtype(primty("unit"), tuplety(list(tvar("b"), tvar("x"))))));
  MonoTypePtr t2(Recursive::make("x", sumtype(primty("unit"), tuplety(list(tvar("c"), tvar("x"))))));
  MonoTypePtr t3(Recursive::make("x", sumtype(primty("unit"), tuplety(list(tvar("d"), tvar("x"))))));
  MonoTypePtr t4(Recursive::make("x", sumtype(primty("unit"), tuplety(list(tvar("e"), tvar("x"))))));
  MonoTypePtr t5(Recursive::make("x", sumtype(primty("unit"), tuplety(list(primty("int"), tvar("x"))))));
  mgu(t4, t5, &u);
  mgu(t2, t3, &u);
  mgu(t0, t1, &u);
  mgu(t1, t2, &u);
  mgu(t3, t4, &u);

  EXPECT_TRUE(*substitute(&u, t0) == *t5);
}


TEST(TypeInf, DecodeRejectsTruncatedInput) {
  // the binary type decoder consumes buffers that can be malformed or truncated
  // (they may arrive from a file or an untrusted network peer), so a short or
  // hostile buffer must throw rather than read out of bounds
  MonoTypePtr ty = tuplety(list(primty("int"), arrayty(primty("char")), tvar("elephant")));

  std::vector<unsigned char> enc;
  encode(ty, &enc);
  EXPECT_TRUE(enc.size() > 0);

  // the full buffer round-trips
  EXPECT_TRUE(show(decode(enc)) == show(ty));

  // every proper-prefix truncation is rejected with an exception, not an
  // out-of-bounds read
  for (size_t k = 0; k < enc.size(); ++k) {
    std::vector<unsigned char> trunc(enc.begin(), enc.begin() + static_cast<long>(k));
    bool threw = false;
    try { decode(trunc); } catch (const std::exception&) { threw = true; }
    EXPECT_TRUE(threw);
  }

  // a length field that overruns the buffer must be rejected rather than trusted:
  // encode a bare type variable ([int tag][size_t namelen][name...]) and rewrite
  // the name length to SIZE_MAX -- the pre-fix code trusted this via a subtraction
  // that underflows once the cursor passes the end of the buffer
  std::vector<unsigned char> craft;
  encode(tvar("x"), &craft);
  EXPECT_TRUE(craft.size() >= sizeof(int) + sizeof(size_t));
  size_t huge = ~static_cast<size_t>(0);
  memcpy(&craft[sizeof(int)], &huge, sizeof(huge));
  bool threw = false;
  try { decode(craft); } catch (const std::exception&) { threw = true; }
  EXPECT_TRUE(threw);
}

TEST(TypeInf, RecordLayoutRejectsUnrepresentableSizes) {
  // A type description can be read from a file or handed over by an untrusted
  // peer, and nothing in it is bounded by what a value in memory could be. The
  // size of a type is computed as an 'unsigned int' and a record member offset
  // is held in an 'int' (with -1 reserved for 'not yet determined'), so a
  // fixed array long enough to run past those used to be multiplied and summed
  // through signed overflow -- undefined behavior -- into a wrapped-around
  // layout. Such a type has no representation here and must be rejected.
  const MonoTypePtr huge(FixedArray::make(primty("long"), MonoTypePtr(TLong::make(std::numeric_limits<long>::max()))));

  // sizing the array on its own is rejected: this is the multiplication that
  // overflowed, 8 bytes an element by a length only the encoding bounds
  EXPECT_EXCEPTION(sizeOf(huge));

  // a length that multiplies out without overflowing, but still to a size no
  // value can have, is out of range just the same
  EXPECT_EXCEPTION(sizeOf(MonoTypePtr(FixedArray::make(primty("char"), MonoTypePtr(TLong::make(0x100000000L))))));

  // as is any record laid out over it
  EXPECT_EXCEPTION(Record::make(list(Record::Member("a", huge))));

  // a negative length describes no array at all
  EXPECT_EXCEPTION(sizeOf(MonoTypePtr(FixedArray::make(primty("char"), MonoTypePtr(TLong::make(-1))))));

  // members that each fit but together run past the end of the layout are
  // rejected too -- here it is the running offset that goes out of range
  const MonoTypePtr big(FixedArray::make(primty("char"), MonoTypePtr(TLong::make(0x40000000))));
  Record::Members ms;
  for (size_t i = 0; i < 4; ++i) {
    ms.push_back(Record::Member(".f" + str::from(i), big));
  }
  EXPECT_EXCEPTION(Record::make(ms));

  // and the same record arriving as an encoded type description -- which is
  // what the binary decoder consumes -- is rejected rather than crashing it
  std::vector<unsigned char> enc;
  auto put = [&](const void* p, size_t n) {
    const auto* b = static_cast<const unsigned char*>(p);
    enc.insert(enc.end(), b, b + n);
  };
  const int          tcode  = Record::type_case_id;
  const size_t       nmems  = 1;
  const size_t       namesz = 1;
  const unsigned int offset = static_cast<unsigned int>(-1); // 'determine this offset'
  put(&tcode,  sizeof(tcode));
  put(&nmems,  sizeof(nmems));
  put(&namesz, sizeof(namesz));
  put("a", 1);
  put(&offset, sizeof(offset));
  encode(huge, &enc);

  bool threw = false;
  try { decode(enc); } catch (const std::exception&) { threw = true; }
  EXPECT_TRUE(threw);

  // ordinary records are laid out as before
  const MonoTypePtr rty =
    Record::make(list(Record::Member("a", primty("char")), Record::Member("b", primty("long"))));
  EXPECT_EQ(sizeOf(rty), 16U);

  const Record* rec = is<Record>(rty);
  EXPECT_TRUE(rec != nullptr);
  EXPECT_EQ(rec->alignedMembers().size(), size_t(3)); // 'a', 7 bytes of padding, 'b'
}

TEST(TypeInf, CodecRejectsInvalidBoolValue) {
  // the stream codec decodes data that can arrive from an untrusted peer;
  // loading any byte other than 0 or 1 into a bool is undefined behavior, so
  // an out-of-range byte must be rejected rather than read into a bool
  for (unsigned int v = 0; v < 256; ++v) {
    std::string raw(1, static_cast<char>(static_cast<unsigned char>(v)));
    std::istringstream in(raw);

    bool x = false;
    bool threw = false;
    try { decode(&x, in); } catch (const std::exception&) { threw = true; }

    if (v <= 1) {
      EXPECT_TRUE(!threw);
      EXPECT_TRUE(x == (v == 1));
    } else {
      EXPECT_TRUE(threw);
    }
  }

  // valid values still round-trip
  for (bool b : {false, true}) {
    std::ostringstream out;
    encode(b, out);
    std::istringstream in(out.str());
    bool r = !b;
    decode(&r, in);
    EXPECT_TRUE(r == b);
  }
}

TEST(TypeInf, CodecRejectsOversizedLength) {
  // a length field taken from untrusted data must be checked against what the
  // input can supply, else a hostile count drives an unbounded allocation
  // before the read that would fail
  std::ostringstream out;
  encode(std::numeric_limits<size_t>::max(), out);   // absurd length, no payload
  out.write("hi", 2);

  {
    std::istringstream in(out.str());
    std::string s;
    bool threw = false;
    try { decode(&s, in); } catch (const std::exception&) { threw = true; }
    EXPECT_TRUE(threw);
  }
  {
    std::istringstream in(out.str());
    std::vector<int> xs;
    bool threw = false;
    try { decode(&xs, in); } catch (const std::exception&) { threw = true; }
    EXPECT_TRUE(threw);
  }

  // well-formed data is unaffected
  std::ostringstream good;
  encode(std::string("elephant"), good);
  std::istringstream gin(good.str());
  std::string s;
  decode(&s, gin);
  EXPECT_TRUE(s == "elephant");
}

TEST(TypeInf, CodecRejectsOversizedLengthOnNonSeekableStream) {
  // The length check above passes over a std::istringstream, which can seek.
  // The stream the RPC path actually decodes expressions over cannot:
  // stream::raw_istream sets its get area with setg() and never overrides
  // seekoff, so tellg() on it fails. A check that consulted only tellg() was
  // therefore inert on exactly the untrusted surface it guards, and a hostile
  // length reached the allocation unchecked.
  std::ostringstream out;
  encode(std::numeric_limits<size_t>::max(), out);   // absurd length, no payload
  out.write("hi", 2);
  const std::string enc = out.str();
  std::vector<uint8_t> raw(enc.begin(), enc.end());

  // the premise: this stream really cannot report a position
  {
    stream::raw_istream<char> in(raw);
    EXPECT_TRUE(in.tellg() == std::streampos(-1));
  }

  // Check the message, not merely that something was thrown: resize() on an
  // absurd count throws std::length_error all by itself, so a test that only
  // asked "did it throw" would pass just as happily with the check removed.
  auto rejectedAsTruncated = [](const std::function<void(std::istream&)>& f,
                                const std::vector<uint8_t>& d) {
    stream::raw_istream<char> in(d);
    try {
      f(in);
    } catch (const std::exception& ex) {
      return std::string(ex.what()).find("truncated") != std::string::npos;
    }
    return false;
  };

  EXPECT_TRUE(rejectedAsTruncated(
    [](std::istream& in) { std::string s; decode(&s, in); }, raw));
  EXPECT_TRUE(rejectedAsTruncated(
    [](std::istream& in) { std::vector<int> xs; decode(&xs, in); }, raw));

  // and a well-formed payload still round-trips over the same stream type
  std::ostringstream good;
  encode(std::string("elephant"), good);
  const std::string genc = good.str();
  std::vector<uint8_t> graw(genc.begin(), genc.end());
  stream::raw_istream<char> gin(graw);
  std::string s;
  decode(&s, gin);
  EXPECT_TRUE(s == "elephant");
}
