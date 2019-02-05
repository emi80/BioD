/*
   This file is part of BioD.
   Copyright (C) 2016   George Githinji <biorelated@gmail.com>
   Copyright (C) 2018   Emilio Palumbo <emiliopalumbo@gmail.com>
   Permission is hereby granted, free of charge, to any person obtaining a
   copy of this software and associated documentation files (the "Software"),
   to deal in the Software without restriction, including without limitation
   the rights to use, copy, modify, merge, publish, distribute, sublicense,
   and/or sell copies of the Software, and to permit persons to whom the
   Software is furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
   DEALINGS IN THE SOFTWARE.
 */

module bio.std.file.fasta;

import std.array;
import std.string;
import std.algorithm;
import std.stdio;
import std.range;
import std.conv;
import std.math;
import std.typecons;
import std.exception;
import std.path;
import std.file;
import std.zlib;
// import bio.std.experimental.hts.bgzf;
import bio.std.file.fai;

/* 
  A text-based single-letter format for representing 
  nucleotide (nt) and amino-acid (aa) sequences.

  The ">" symbol/character marks the start of a fasta entry.
  Each fasta entry comprise of an alphanumeric definition line followed by a 
  newline character and a single or multiline sequence of IUPAC codes used to
  represent nucleotide or amino-acid sequences.

  An example of a nucleotide fasta file 
  
  >Entry1_ID header field1|field2|...
  TTGACGGGTTTTTGTCCTGATT
 
  >Entry2_ID header field1|field2|...
  ATTTTGGGTTACTGTTGGTTTTTGGGC

  TODO: 
 1. Allow reading gzipped fasta files.
 
*/  

struct FastaRecord {
    string header;
    string sequence;
    ulong lineLen;
    string lineTerm = "\n";
    
    // split the header to array of fields 
    @property string[] headerFields(){
        return split(header, "|").map!strip.array;
    }

    // return the length of the sequence
    @property ulong len() {
        return sequence.length;
    }

    string toString() {
        string seq;
        ulong i = lineLen;
        for (; i<sequence.length; i+=lineLen) {
            seq~=sequence[i-lineLen..i]~"\n";
        }
        seq~=sequence[i-lineLen..$];
        return format(">%s\n%s", header, seq);
    }
   
    unittest {
        auto recString = q"(
            >chr2
            acgtgagtgcacgtgagtgcacgtgagtgc
            acgtgagtgcacgtgagtgc
        )".outdent().strip();
        auto header = "chr2";
        auto seq = "acgtgagtgcacgtgagtgcacgtgagtgcacgtgagtgcacgtgagtgc";
        auto lineLen = 30;
        auto rec = FastaRecord(header, seq, lineLen);
        assert (rec.toString() == recString);
        assert (rec.len == seq.length);

    }
}

struct Region {
    string reference;
    ulong beg, end;
    @property len() {
        return end - beg;
    }
    
    string toString() {
        if ( end == 0 ) {
            if ( beg == 0 )
                return reference;
            else
                return format("%s:%s", reference, beg+1);
        }
        return format("%s:%s-%s", reference, beg+1, end);
    }
    
    this(string q) {
        auto res = q.split(":");
        reference = res[0];
        if ( res.length > 2) {
            throw new Exception(format("Wrong format for region: %s", q));
        } else if (res.length > 1) {
            auto boundaries = res[1].replace(",","").split("-").map!(to!ulong);
            beg = boundaries[0]-1;
            if ( boundaries.length == 2 ) {
                end = boundaries[1];
            }
        }
    }

    unittest {
        assert ( Region("chr2:1-10").toString() == "chr2:1-10" );
        assert ( Region("chr2:1-10").len == 10 );
        assert ( Region("chr2").toString() == "chr2" );
        assert ( Region("chr2:10").toString() == "chr2:10" );
        assertThrown!Exception( Region("chr2:1:10") );

        auto region1 = Region("chr1:1,000-2000");
        assert(region1.reference == "chr1");
        assert(region1.beg == 999);
        assert(region1.end == 2000);

        auto region2 = Region("chr2");
        assert(region2.reference == "chr2");
        assert(region2.beg == 0);
        assert(region2.end == 0);

        auto region3 = Region("chr3:1,000,000");
        assert(region3.reference == "chr3");
        assert(region3.beg == 999_999);
        assert(region3.end == 0);
    }
}

struct FastaIterator {
    File f;
    bool gzipped;
    string lineTerm = "\n";
    FastaRecord current, next;

    struct Reader {
        File f;
        bool gzipped;
        KeepTerminator kt = KeepTerminator.no;
        string lineTerm = "\n", line;
        ubyte[] remind;
        ubyte[][] buffer;
        UnCompress decmp = new UnCompress();

        @property bool empty() {
            return f.eof && buffer.empty;
        }

        @property ref string front() {
            if (line.empty) {
                popFront();              
            }
            return line;
        }

        void popFront() {
            if ( buffer.length == 0 ) {
                foreach (chunk; f.byChunk(4096)) {
                    if ( gzipped )
                        chunk = cast(ubyte[])decmp.uncompress(chunk);
                    buffer = chunk.dup.split(lineTerm);
                    if ( remind ) {
                        buffer[0]=remind~buffer[0];
                    }
                    if ( countUntil(retro(chunk), lineTerm) ) {
                        remind = buffer[$-1];
                        buffer = buffer[0..$-1];
                    }
                    break;
                }
            }
            foreach (l; buffer) {
                line = cast(string)l;
                buffer = buffer[1..$];
                break;
            }
        }
    }

    unittest {
        auto testFa = tempDir.buildPath("test.fa");
        scope(exit) testFa.remove;
        File(testFa, "w").writeln(q"(
            >chr1
            acgtgagtgc
            >chr2
            acgtgagtgcacgtgagtgcacgtgagtgc
            acgtgagtgcacgtgagtgc
            >chr3 hrsv | Kilifi | partial sequence
            CATGTTATTACAAGTAGTGATATTTGCCCTAATAATAATATTGTAGTGAAATCCAATTTCACAACAATGC
        )".outdent().strip());
        auto r = Reader(File(testFa));
        r.lineTerm = "\t";

        ubyte[] gzip = [
            0x1f, 0x8b, 0x08, 0x08, 0xa8, 0x78, 0xf2, 0x5b, 0x00, 0x03, 0x74, 0x31, 0x2e, 0x66, 0x61, 0x00,
            0x6d, 0x4b, 0x39, 0x0a, 0x80, 0x30, 0x10, 0xec, 0xf3, 0x8a, 0x7c, 0x41, 0xed, 0x85, 0x65, 0x8b,
            0x2d, 0x6c, 0xf7, 0x03, 0x21, 0x44, 0x0d, 0x88, 0x68, 0x3c, 0x2a, 0x1f, 0xef, 0x44, 0x11, 0x2c,
            0x02, 0x33, 0x30, 0x67, 0xeb, 0xc7, 0x54, 0x19, 0xe7, 0x87, 0x7d, 0x70, 0xa0, 0x37, 0x2d, 0x82,
            0xfa, 0x17, 0x94, 0x54, 0xb1, 0x7e, 0x9e, 0x8d, 0x1d, 0xd3, 0x76, 0xda, 0xcb, 0x76, 0x71, 0x8a,
            0x7d, 0x84, 0x58, 0x5c, 0xda, 0xa3, 0x9b, 0xec, 0x16, 0xd6, 0x23, 0xcc, 0x3e, 0x18, 0x26, 0x15,
            0x55, 0x02, 0x98, 0x48, 0x14, 0x10, 0xca, 0x56, 0x85, 0x99, 0x95, 0xe8, 0x03, 0x82, 0xb7, 0x84,
            0x61, 0x4c, 0xb1, 0xe0, 0x7c, 0xc9, 0x52, 0xd8, 0xdc, 0x43, 0x6d, 0x5b, 0xc0, 0xb9, 0x00, 0x00,
            0x00
        ];
        auto testFaGz = tempDir.buildPath("test.fa.gz");
        scope(exit) testFaGz.remove;
        File(testFaGz, "w").rawWrite(gzip);
        // foreach (ubyte[] read; BgzfBlocks(testFaGz)) {
        //     writeln(cast(string)read); // raw unpacking
        // }
        r = Reader(File(testFaGz), true);
        // foreach(l; r) {
        //     writeln(l);
        // }
    }

    this(string filename) {
        f = File(filename);
        detectLineTerm();
        isGzipped();
    }

    void isGzipped() {
        auto pos = f.tell;
        f.rewind();
        auto magic = f.rawRead(new ubyte[2]);
        gzipped = ( magic[0] == to!ubyte(0x1f) && magic[1] == to!ubyte(0x8b) );
        f.seek(pos);
    }

    void detectLineTerm() {
        lineTerm = readLines(KeepTerminator.yes)
                           .take(1)
                           .front
                           .endsWith("\r\n") ? "\r\n" : "\n";
        f.rewind();
    }

    auto readLines(KeepTerminator kt = KeepTerminator.no) {
        return f.byLine(kt, lineTerm);
    }

    @property bool empty() {
        return f.eof && current.len == 0;
    }

    @property ref FastaRecord front() {
        if ( current.len == 0 ) {
            popFront();
        }
        return current;
    }

    void popFront() {
        current = next;
        foreach(line; readLines()) {
            if ( line.startsWith(">") ) {
                if ( current.len > 0 ) {
                    next = FastaRecord();
                    next.lineTerm = lineTerm;
                    next.header ~= line[1..$];
                    break;
                }
                current.lineTerm = lineTerm;
                current.header ~= line[1..$];
            } else {
                if ( current.lineLen == 0 ) {
                    current.lineLen = line.length;
                }
                current.sequence ~= line;
            }
        }
    }
}

unittest {
    auto testFa = tempDir.buildPath("test.fa");
    scope(exit) testFa.remove;
    File(testFa, "w").writeln(q"(
        >chr1
        acgtgagtgc
        >chr2
        acgtgagtgcacgtgagtgcacgtgagtgc
        acgtgagtgcacgtgagtgc
        >chr3 hrsv | Kilifi | partial sequence
        CATGTTATTACAAGTAGTGATATTTGCCCTAATAATAATATTGTAGTGAAATCCAATTTCACAACAATGC
    )".outdent().strip());
    assert ( FastaIterator(testFa).gzipped == false );
    auto records = FastaIterator(testFa).array;
    assert ( records.length == 3 );
    assert ( records[0].header == "chr1" );
    assert ( records[0].sequence == "acgtgagtgc" );
    assert ( records[0].lineLen == 10 );
    assert ( records[0].toString == q"(
        >chr1
        acgtgagtgc
    )".outdent().strip());
    assert ( records[1].header == "chr2" );
    assert ( records[1].sequence == "acgtgagtgcacgtgagtgcacgtgagtgcacgtgagtgcacgtgagtgc" );
    assert ( records[1].lineLen == 30 );
    assert ( records[1].toString == q"(
        >chr2
        acgtgagtgcacgtgagtgcacgtgagtgc
        acgtgagtgcacgtgagtgc
    )".outdent().strip());

    assert(records[2].header == "chr3 hrsv | Kilifi | partial sequence");
    assert(records[2].headerFields.length == 3);
    assert(records[2].headerFields == ["chr3 hrsv","Kilifi","partial sequence"]);

    ubyte[] gzip = [
        0x1f, 0x8b, 0x08, 0x08, 0xa8, 0x78, 0xf2, 0x5b, 0x00, 0x03, 0x74, 0x31, 0x2e, 0x66, 0x61, 0x00,
        0x6d, 0x4b, 0x39, 0x0a, 0x80, 0x30, 0x10, 0xec, 0xf3, 0x8a, 0x7c, 0x41, 0xed, 0x85, 0x65, 0x8b,
        0x2d, 0x6c, 0xf7, 0x03, 0x21, 0x44, 0x0d, 0x88, 0x68, 0x3c, 0x2a, 0x1f, 0xef, 0x44, 0x11, 0x2c,
        0x02, 0x33, 0x30, 0x67, 0xeb, 0xc7, 0x54, 0x19, 0xe7, 0x87, 0x7d, 0x70, 0xa0, 0x37, 0x2d, 0x82,
        0xfa, 0x17, 0x94, 0x54, 0xb1, 0x7e, 0x9e, 0x8d, 0x1d, 0xd3, 0x76, 0xda, 0xcb, 0x76, 0x71, 0x8a,
        0x7d, 0x84, 0x58, 0x5c, 0xda, 0xa3, 0x9b, 0xec, 0x16, 0xd6, 0x23, 0xcc, 0x3e, 0x18, 0x26, 0x15,
        0x55, 0x02, 0x98, 0x48, 0x14, 0x10, 0xca, 0x56, 0x85, 0x99, 0x95, 0xe8, 0x03, 0x82, 0xb7, 0x84,
        0x61, 0x4c, 0xb1, 0xe0, 0x7c, 0xc9, 0x52, 0xd8, 0xdc, 0x43, 0x6d, 0x5b, 0xc0, 0xb9, 0x00, 0x00,
        0x00
    ];
    auto testFaGz = tempDir.buildPath("test.fa.gz");
    scope(exit) testFaGz.remove;
    File(testFaGz, "w").rawWrite(gzip);
    assert ( FastaIterator(testFaGz).gzipped == true );
    records = FastaIterator(testFaGz).array;
}

auto fastaRecords(string filename) {

    File f = File(filename);
    FastaRecord[] records; 
    string lineTerm = f.byLine(KeepTerminator.yes).take(1).front.endsWith("\r\n") ? "\r\n" : "\n";
    f.seek(0);
    // ulong offset;
    foreach(line; f.byLine(KeepTerminator.no, lineTerm)) {
        // offset+= line.length + lineTerm.length;
        if ( line.startsWith(">") ) {
            records~=FastaRecord();
            records[$-1].lineTerm = lineTerm;
            records[$-1].header ~= line[1..$];
        } else {
            if ( records[$-1].lineLen == 0 ) {
                records[$-1].lineLen = line.length;
            }
            records[$-1].sequence ~= line;
        }
    }

    return records;
}

unittest {
    auto testFa = tempDir.buildPath("test.fa");
    scope(exit) testFa.remove;
    File(testFa, "w").writeln(q"(
        >chr1
        acgtgagtgc
        >chr2
        acgtgagtgcacgtgagtgcacgtgagtgc
        acgtgagtgcacgtgagtgc
        >chr3 hrsv | Kilifi | partial sequence
        CATGTTATTACAAGTAGTGATATTTGCCCTAATAATAATATTGTAGTGAAATCCAATTTCACAACAATGC
    )".outdent().strip());
    auto records = fastaRecords(testFa);
    assert ( records.length == 3 );
    assert ( records[0].header == "chr1" );
    assert ( records[0].sequence == "acgtgagtgc" );
    assert ( records[0].lineLen == 10 );
    assert ( records[0].toString == q"(
        >chr1
        acgtgagtgc
    )".outdent().strip());
    assert ( records[1].header == "chr2" );
    assert ( records[1].sequence == "acgtgagtgcacgtgagtgcacgtgagtgcacgtgagtgcacgtgagtgc" );
    assert ( records[1].lineLen == 30 );
    assert ( records[1].toString == q"(
        >chr2
        acgtgagtgcacgtgagtgcacgtgagtgc
        acgtgagtgcacgtgagtgc
    )".outdent().strip());

    assert(records[2].header == "chr3 hrsv | Kilifi | partial sequence" );
    assert(records[2].headerFields.length == 3);
    assert(records[2].headerFields == ["chr3 hrsv","Kilifi","partial sequence"]);
}

auto fastaRegions(string filename, string[] queries) {
    File f = File(filename);
    FaiRecord[string] index = makeIndex(readFai(filename~=".fai"));
    Region[] regions = to!(Region[])(queries);
    return fetchFastaRegions(f, index, regions);
}

auto fetchFastaRegions(File fasta, FaiRecord[string] index, Region[] regions) {

    FastaRecord[] records;

    foreach (region; regions) {
        string seq;
        ulong len;
        if ( region.reference in index ) {
            auto reference = index[region.reference];
            fasta.seek(reference.offset+region.beg+region.beg/reference.lineLen);
            size_t bufLen;
            if ( region.end == 0 ) 
                bufLen = reference.seqLen + reference.seqLen/reference.lineLen;
            else
                bufLen = region.len + region.len/reference.lineLen;
            seq = fasta.rawRead(new char[bufLen]).replace(reference.lineTerm,"").idup;
            len = reference.lineLen;
        }
        records ~= FastaRecord(region.to!string, seq, len);
    }

    return records;    
}

unittest {
    auto testFa = tempDir.buildPath("test.fa");
    scope(exit) testFa.remove;
    File(testFa, "w").writeln(q"(
        >chr1
        acgtgagtgc
        >chr2
        acgtgagtgcacgtgagtgcacgtgagtgc
        acgtgagtgcacgtgagtgc
    )".outdent().strip());
    auto faiString = "
        chr1\t10\t6\t10\t11
        chr2\t50\t23\t30\t31
    ".outdent().strip();
    auto testIndex = tempDir.buildPath("test.fa.fai");
    scope(exit) testIndex.remove;
    File(testIndex, "w").writeln(faiString);
    
    auto regions = fastaRegions(testFa, ["chr1:4-6", "chr2:36-45"]);
    assert ( regions.length == 2 );
    assert ( regions[0].header == "chr1:4-6" );
    assert ( regions[0].len == 3 );
    assert ( regions[0].sequence == "tga" );
    assert ( regions[0].lineLen == 10 );
    assert ( regions[1].header == "chr2:36-45" );
    assert ( regions[1].len == 10 );
    assert ( regions[1].sequence == "agtgcacgtg" );
    assert ( regions[1].lineLen == 30 );
    
    regions = fastaRegions(testFa, ["chr1"]);
    assert ( regions.length == 1 );
    assert ( regions[0].header == "chr1" );
    assert ( regions[0].len == 10 );
    assert ( regions[0].sequence == "acgtgagtgc" );
    assert ( regions[0].lineLen == 10 );
    
    regions = fastaRegions(testFa, ["chr2"]);
    assert ( regions.length == 1 );
    assert ( regions[0].header == "chr2" );
    assert ( regions[0].len == 50 );
    assert ( regions[0].sequence == "acgtgagtgcacgtgagtgcacgtgagtgcacgtgagtgcacgtgagtgc" );
    assert ( regions[0].lineLen == 30 );
}
