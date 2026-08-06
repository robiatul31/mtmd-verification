#!/usr/bin/perl
#
#  mtmd_verify.pl -- verification suite for the paper
#
#     "A Forcing Mechanism for the Mixed Triple Metric Dimension of Plane Graphs"
#
#  This single program reproduces every row of the verification table
#  (Table "Ranges verified") in the Computational Verification section.
#
#  DEFINITIONS IMPLEMENTED
#  -----------------------
#  For a plane graph G, every element x of V(G) u E(G) u F(G) is stored as the
#  list V(x) of vertices incident with it: V(v)={v}, V(uv)={u,v}, and V(f) the
#  vertex set of the face f.  Distances are then
#
#        d(s,x) = min { d(s,u) : u in V(x) }                (Defs. 2.2, 2.3)
#
#  A set S of vertices is a mixed triple resolving set if the code
#  (d(s,x))_{s in S} is distinct for distinct elements x; MTMD(G) is the least
#  size of such a set.  Restricting the element list to V(G) u E(G) gives the
#  mixed metric dimension mmd(G).
#
#  The forcing criterion of Theorem 3.3 is
#
#        N(w) subset of N[u] u N[v]   ==>   w is the unique separator of (e,f)
#
#  for a triangular face f={u,v,w} bounded by e=uv; F(G) is the set of vertices
#  forced in this way.
#
#  USAGE
#  -----
#      perl mtmd_verify.pl              # full run, ranges as in the paper
#      perl mtmd_verify.pl --quick      # reduced ranges, ~10 seconds
#      perl mtmd_verify.pl --only=NAME  # run a single check (see list below)
#      perl mtmd_verify.pl --list       # list check names
#
#  Every check prints one line per parameter value and ends with OK or FAIL.
#  The program exits with status 0 only if every check passed.
#
#  All arithmetic is exact integer arithmetic; no floating-point computation
#  occurs anywhere.  The program has no dependencies beyond core Perl.
#
#  Licence: CC0 / public domain.  Verified with Perl 5.32.
#

use strict;
use warnings;

my $QUICK = 0;
my $ONLY  = '';
for my $arg (@ARGV) {
    if    ($arg eq '--quick')      { $QUICK = 1 }
    elsif ($arg =~ /^--only=(.+)$/) { $ONLY = $1 }
    elsif ($arg eq '--list')       { list_checks(); exit 0 }
    else { die "unknown argument '$arg'\n" }
}

my $FAILURES = 0;

# =====================================================================
#  GENERIC GRAPH MACHINERY
# =====================================================================

# A graph is a hashref:
#   V   => [ vertex names ]
#   E   => [ [u,v], ... ]
#   F   => [ [v1,...,vk], ... ]     (all faces, bounded and unbounded)
#   ADJ => { v => [neighbours] }
sub mk_graph {
    my ($V, $E, $F) = @_;
    my %adj = map { $_ => [] } @$V;
    for my $e (@$E) {
        push @{ $adj{ $e->[0] } }, $e->[1];
        push @{ $adj{ $e->[1] } }, $e->[0];
    }
    return { V => $V, E => $E, F => $F, ADJ => \%adj };
}

# all-pairs distances by BFS from every vertex
sub distances {
    my ($G) = @_;
    my %D;
    for my $s (@{ $G->{V} }) {
        my %d = ($s => 0);
        my @q = ($s);
        while (@q) {
            my $x = shift @q;
            for my $y (@{ $G->{ADJ}{$x} }) {
                next if exists $d{$y};
                $d{$y} = $d{$x} + 1;
                push @q, $y;
            }
        }
        $D{$s} = \%d;
    }
    return \%D;
}

# element list: [ [label, [incident vertices]], ... ]
# $kind: 'triple' = V u E u F ; 'mixed' = V u E
sub element_list {
    my ($G, $kind) = @_;
    my @els;
    push @els, [ "v:$_", [$_] ] for @{ $G->{V} };
    my $i = 0;
    push @els, [ 'e:' . $i++, [ @$_ ] ] for @{ $G->{E} };
    if (($kind // 'triple') eq 'triple') {
        my $j = 0;
        push @els, [ 'f:' . $j++, [ @$_ ] ] for @{ $G->{F} };
    }
    return \@els;
}

sub elem_code {
    my ($D, $S, $verts) = @_;
    my @c;
    for my $s (@$S) {
        my $m;
        for my $u (@$verts) {
            my $d = $D->{$s}{$u};
            $m = $d if !defined($m) || $d < $m;
        }
        push @c, $m;
    }
    return join(',', @c);
}

# does S resolve every element?  returns (1) or (0, labelA, labelB)
sub resolves {
    my ($D, $S, $els) = @_;
    my %seen;
    for my $el (@$els) {
        my $k = elem_code($D, $S, $el->[1]);
        return (0, $el->[0], $seen{$k}) if exists $seen{$k};
        $seen{$k} = $el->[0];
    }
    return (1);
}

# iterate over all k-subsets of 0..$n-1, calling $cb->(\@idx); stop if cb returns 1
sub each_subset {
    my ($n, $k, $cb) = @_;
    return if $k > $n;
    my @idx = (0 .. $k - 1);
    while (1) {
        return 1 if $cb->(\@idx);
        my $i = $k - 1;
        $i-- while $i >= 0 && $idx[$i] == $n - $k + $i;
        return 0 if $i < 0;
        $idx[$i]++;
        $idx[$_] = $idx[$_ - 1] + 1 for ($i + 1 .. $k - 1);
    }
}

# smallest resolving set size, searching k = 1,2,3,...  ($cap = give up beyond)
sub min_resolving_size {
    my ($G, $kind, $cap) = @_;
    my $D    = distances($G);
    my $els  = element_list($G, $kind);
    my $V    = $G->{V};
    my $n    = scalar @$V;
    $cap = $n unless defined $cap;
    for my $k (1 .. $cap) {
        my $found;
        each_subset($n, $k, sub {
            my ($idx) = @_;
            my @S = map { $V->[$_] } @$idx;
            my ($ok) = resolves($D, \@S, $els);
            $found = [@S] if $ok;
            return $ok ? 1 : 0;
        });
        return ($k, $found) if $found;
    }
    return (-1, undef);
}

# verify that NO subset of size < k resolves (this is the lower-bound half)
sub no_resolving_below {
    my ($G, $kind, $k) = @_;
    my $D   = distances($G);
    my $els = element_list($G, $kind);
    my $V   = $G->{V};
    my $n   = scalar @$V;
    for my $m (1 .. $k - 1) {
        my $bad;
        each_subset($n, $m, sub {
            my ($idx) = @_;
            my @S = map { $V->[$_] } @$idx;
            my ($ok) = resolves($D, \@S, $els);
            $bad = [@S] if $ok;
            return $ok ? 1 : 0;
        });
        return (0, $bad) if $bad;
    }
    return (1);
}

# all vertices separating the pair (e,f) where f = e + apex w
sub separators_of_apex_pair {
    my ($G, $D, $u, $v, $w) = @_;
    my @sep;
    for my $s (@{ $G->{V} }) {
        my $de = $D->{$s}{$u} < $D->{$s}{$v} ? $D->{$s}{$u} : $D->{$s}{$v};
        push @sep, $s if $D->{$s}{$w} < $de;
    }
    return @sep;
}

# the neighbourhood containment N(w) subset N[u] u N[v]
sub containment_holds {
    my ($G, $u, $v, $w) = @_;
    my %M = map { $_ => 1 } (@{ $G->{ADJ}{$u} }, $u, @{ $G->{ADJ}{$v} }, $v);
    for my $x (@{ $G->{ADJ}{$w} }) { return 0 unless $M{$x} }
    return 1;
}

# forced set F(G) together with a per-pair audit of Theorem 3.3
sub forced_set_audit {
    my ($G) = @_;
    my $D = distances($G);
    my (%forced, $violations, $pairs);
    $violations = 0;
    $pairs      = 0;
    for my $f (@{ $G->{F} }) {
        next unless @$f == 3;                      # triangular faces only
        my ($x, $y, $z) = @$f;
        for my $perm ([$x,$y,$z], [$y,$z,$x], [$z,$x,$y]) {
            my ($u, $v, $w) = @$perm;
            $pairs++;
            my @sep  = separators_of_apex_pair($G, $D, $u, $v, $w);
            my $cont = containment_holds($G, $u, $v, $w);
            # Theorem 3.3: containment ==> unique separator (and it is w)
            $violations++ if $cont && !(@sep == 1 && $sep[0] eq $w);
            $forced{ $sep[0] } = 1 if @sep == 1;
        }
    }
    return (\%forced, $violations, $pairs);
}

# =====================================================================
#  GRAPH CONSTRUCTORS
# =====================================================================

# Prism Pr_n = C_n x P_2 (kept separate for readability; equals stacked(n,2))
sub prism {
    my ($n) = @_;
    my @V = (map("a$_", 0 .. $n-1), map("b$_", 0 .. $n-1));
    my (@E, @F);
    for my $i (0 .. $n-1) {
        my $j = ($i + 1) % $n;
        push @E, ["a$i","a$j"], ["b$i","b$j"], ["a$i","b$i"];
        push @F, ["a$i","a$j","b$j","b$i"];               # quadrilateral Q_i
    }
    push @F, [ map("a$_", 0 .. $n-1) ], [ map("b$_", 0 .. $n-1) ];
    return mk_graph(\@V, \@E, \@F);
}

# Antiprism A_n, diagonals a_i b_i and a_{i+1} b_i
sub antiprism {
    my ($n) = @_;
    my @V = (map("a$_", 0 .. $n-1), map("b$_", 0 .. $n-1));
    my (@E, @F);
    for my $i (0 .. $n-1) {
        my $j = ($i + 1) % $n;
        push @E, ["a$i","a$j"], ["b$i","b$j"], ["a$i","b$i"], ["a$j","b$i"];
        push @F, ["a$i","a$j","b$i"];                     # f_i
        push @F, ["b$i","b$j","a$j"];                     # f'_i
    }
    push @F, [ map("a$_", 0 .. $n-1) ], [ map("b$_", 0 .. $n-1) ];
    return mk_graph(\@V, \@E, \@F);
}

# Stacked prism C_n x P_r  (r=2 is Pr_n, r=3 is M_n)
sub stacked {
    my ($n, $r) = @_;
    my @V;
    for my $j (0 .. $r-1) { push @V, "v${j}_$_" for 0 .. $n-1 }
    my (@E, @F);
    for my $j (0 .. $r-1) {
        for my $i (0 .. $n-1) {
            my $i2 = ($i + 1) % $n;
            push @E, ["v${j}_$i", "v${j}_$i2"];           # layer edge A_i^{(j)}
        }
    }
    for my $j (0 .. $r-2) {
        for my $i (0 .. $n-1) {
            push @E, ["v${j}_$i", "v" . ($j+1) . "_$i"];  # rung R_i^{(j)}
        }
    }
    for my $j (0 .. $r-2) {
        for my $i (0 .. $n-1) {
            my $i2 = ($i + 1) % $n;
            push @F, ["v${j}_$i", "v${j}_$i2",
                      "v" . ($j+1) . "_$i2", "v" . ($j+1) . "_$i"];
        }
    }
    push @F, [ map { "v0_$_" }        0 .. $n-1 ];
    push @F, [ map { "v" . ($r-1) . "_$_" } 0 .. $n-1 ];
    return mk_graph(\@V, \@E, \@F);
}

# Icosahedron: 0 and 11 antipodal; 1..5 and 6..10 the two pentagons;
# upper vertex 1+i joined to lower vertices 6+i and 6+((i+4) mod 5).
sub icosahedron {
    my @V = (0 .. 11);
    my @E;
    push @E, [0, $_]  for 1 .. 5;
    push @E, [11, $_] for 6 .. 10;
    for my $i (0 .. 4) {
        push @E, [1 + $i, 1 + (($i + 1) % 5)];
        push @E, [6 + $i, 6 + (($i + 1) % 5)];
        push @E, [1 + $i, 6 + $i];
        push @E, [1 + $i, 6 + (($i + 4) % 5)];
    }
    my @F;
    for my $i (0 .. 4) {
        push @F, [0, 1 + $i, 1 + (($i + 1) % 5)];
        push @F, [11, 6 + $i, 6 + (($i + 1) % 5)];
        push @F, [1 + $i, 6 + (($i + 4) % 5), 6 + $i];
        push @F, [1 + $i, 1 + (($i + 1) % 5), 6 + $i];
    }
    return mk_graph(\@V, \@E, \@F);
}

# n-gonal bipyramid B_n: cycle c_0..c_{n-1} plus two apices N,S
sub bipyramid {
    my ($n) = @_;
    my @V = (map("c$_", 0 .. $n-1), "N", "S");
    my (@E, @F);
    for my $i (0 .. $n-1) {
        my $j = ($i + 1) % $n;
        push @E, ["c$i","c$j"], ["c$i","N"], ["c$i","S"];
        push @F, ["c$i","c$j","N"], ["c$i","c$j","S"];
    }
    return mk_graph(\@V, \@E, \@F);
}

# =====================================================================
#  CYCLIC HELPERS (window calculus of Section 5)
# =====================================================================

sub cyc  { my ($a,$b,$n) = @_; my $d = abs($a - $b) % $n; return $d < $n - $d ? $d : $n - $d }
sub in_W { my ($k,$i,$n,$c) = @_; return ((($i - $k) % $n) <= $c - 1) ? 1 : 0 }
sub mu   { my ($k,$i,$n) = @_; my $a = cyc($k,$i,$n); my $b = cyc($k,($i+1)%$n,$n); return $a < $b ? $a : $b }

# =====================================================================
#  CHECKS -- one per row of the verification table
# =====================================================================

my @CHECKS;   # [ name, description, coderef ]

sub register { push @CHECKS, [@_] }
sub list_checks {
    print "available checks:\n";
    print "  $_->[0]\n" for @CHECKS;
}
sub report {
    my ($name, $ok, $detail) = @_;
    $detail = defined $detail ? "  ($detail)" : '';
    printf "  %-6s %s%s\n", ($ok ? '[ OK ]' : '[FAIL]'), $name, $detail;
    $FAILURES++ unless $ok;
}

# ---------------------------------------------------------------- row 1
register('prism-exhaustive',
  'MTMD(Pr_n) = 4, exhaustive',
  sub {
    my $hi = $QUICK ? 9 : 25;
    my $ok = 1;
    for my $n (3 .. $hi) {
        my $G = prism($n);
        my ($lb) = no_resolving_below($G, 'triple', 4);
        my $c = int(($n + 1) / 2);
        my @S = ("a0", "a1", "a$c", "b0");
        my ($ub) = resolves(distances($G), \@S, element_list($G, 'triple'));
        my $good = $lb && $ub;
        $ok &&= $good;
        printf "    n=%-3d no 3-set resolves: %-3s  witness {a0,a1,a%d,b0} resolves: %-3s\n",
               $n, ($lb ? 'yes' : 'NO'), $c, ($ub ? 'yes' : 'NO');
    }
    return ($ok, "3 <= n <= $hi");
  });

# ---------------------------------------------------------------- row 2
register('prism-construction',
  'S = {a_0,a_1,a_c,b_0} resolves Pr_n',
  sub {
    my $hi = $QUICK ? 12 : 45;
    my $ok = 1;
    for my $n (3 .. $hi) {
        my $G = prism($n);
        my $c = int(($n + 1) / 2);
        my @S = ("a0", "a1", "a$c", "b0");
        my ($r, $x, $y) = resolves(distances($G), \@S, element_list($G, 'triple'));
        $ok &&= $r;
        print "    n=$n  COLLISION $x = $y\n" unless $r;
    }
    return ($ok, "3 <= n <= $hi");
  });

# ---------------------------------------------------------------- row 3
register('antiprism',
  'MTMD(A_n) = 2n; every vertex is the unique separator of some pair',
  sub {
    my $hi = $QUICK ? 8 : 25;
    my $ok = 1;
    for my $n (3 .. $hi) {
        my $G = antiprism($n);
        my ($forced, $viol) = forced_set_audit($G);
        my $all = (scalar(keys %$forced) == scalar @{ $G->{V} });
        # upper bound: V(G) itself resolves
        my ($full) = resolves(distances($G), $G->{V}, element_list($G, 'triple'));
        my $good = $all && $full && !$viol;
        $ok &&= $good;
        printf "    n=%-3d |F(A_n)|=%-3d of %-3d  V resolves: %-3s  Thm 3.3 violations: %d\n",
               $n, scalar(keys %$forced), scalar @{ $G->{V} },
               ($full ? 'yes' : 'NO'), $viol;
    }
    return ($ok, "3 <= n <= $hi");
  });

# ---------------------------------------------------------------- rows 4,5,6
register('stacked-exhaustive',
  'MTMD(C_n x P_r) = 4 (includes Pr_n at r=2 and M_n at r=3)',
  sub {
    my ($hiN, $hiR) = $QUICK ? (6, 3) : (8, 5);
    my $ok = 1;
    for my $r (2 .. $hiR) {
        for my $n (3 .. $hiN) {
            my $G = stacked($n, $r);
            my ($lb) = no_resolving_below($G, 'triple', 4);
            my $c = int(($n + 1) / 2);
            my @S = ("v0_0", "v0_1", "v0_$c", "v" . ($r - 1) . "_0");
            my ($ub) = resolves(distances($G), \@S, element_list($G, 'triple'));
            my $good = $lb && $ub;
            $ok &&= $good;
            printf "    n=%-2d r=%-2d  no 3-set resolves: %-3s  witness resolves: %-3s\n",
                   $n, $r, ($lb ? 'yes' : 'NO'), ($ub ? 'yes' : 'NO');
        }
    }
    return ($ok, "3 <= n <= $hiN, 2 <= r <= $hiR");
  });

# ---------------------------------------------------------------- row 7
register('stacked-case-structure',
  'case structure of the C_n x P_r lower bound is exhaustive and fires',
  sub {
    my ($hiN, $hiR) = $QUICK ? (9, 4) : (16, 6);
    my %tally; my $fail = 0;
    for my $n (3 .. $hiN) {
        my $c = int(($n + 1) / 2);
        for my $r (2 .. $hiR) {
            my @Vs;
            for my $j (0 .. $r-1) { for my $i (0 .. $n-1) { push @Vs, [$i, $j] } }
            my $N = scalar @Vs;
            each_subset($N, 3, sub {
                my ($idx) = @_;
                my @S = map { $Vs[$_] } @$idx;
                # Step 1 of the proof: both extreme layers must be occupied
                return 0 unless (grep { $_->[1] == 0 }      @S)
                            and (grep { $_->[1] == $r - 1 } @S);
                # choose the cut exactly as the proof prescribes
                my @L0 = grep { $_->[1] == 0 }      @S;
                my @LR = grep { $_->[1] == $r - 1 } @S;
                my (@pair, @sing);
                if (@L0 >= 2) {
                    @pair = @L0[0,1];
                    @sing = grep { $_ != $L0[0] && $_ != $L0[1] } @S;
                } elsif (@LR >= 2) {
                    @pair = @LR[0,1];
                    @sing = grep { $_ != $LR[0] && $_ != $LR[1] } @S;
                } else {
                    my ($mid) = grep { $_->[1] != 0 && $_->[1] != $r - 1 } @S;
                    @pair = ($L0[0], $mid);
                    @sing = @LR;
                }
                my ($p, $q) = ($pair[0][0], $pair[1][0]);
                my $s = $sing[0][0];
                my $d = cyc($p, $q, $n);

                # Case 1: all three positions in a common window
                for my $i (0 .. $n-1) {
                    if (in_W($p,$i,$n,$c) && in_W($q,$i,$n,$c) && in_W($s,$i,$n,$c)) {
                        $tally{'case 1'}++; return 0;
                    }
                }
                # Case 2: d <= c-1, some window holds p,q but not s
                if ($d <= $c - 1) {
                    for my $i (0 .. $n-1) {
                        if (in_W($p,$i,$n,$c) && in_W($q,$i,$n,$c) && !in_W($s,$i,$n,$c)) {
                            $tally{'case 2'}++; return 0;
                        }
                    }
                    $fail++; return 0;
                }
                # Case 3 forces n even and q = p + n/2
                if ($d != $c || $n % 2) { $fail++; return 0 }
                if ($s != $p && $s != $q) {
                    for my $i (0 .. $n-1) {
                        my $im = ($i - 1 + $n) % $n;
                        next unless mu($p,$i,$n) == mu($p,$im,$n);
                        next unless mu($q,$i,$n) == mu($q,$im,$n);
                        next unless mu($s,$im,$n) == mu($s,$i,$n) + 1;
                        $tally{'case 3a'}++; return 0;
                    }
                    $fail++; return 0;
                } else {
                    for my $t (0 .. $n-1) {
                        my $all = 1;
                        for my $z (@S) { $all = 0 unless ((2*$t - $z->[0]) % $n) == $z->[0] }
                        if ($all) { $tally{'case 3b'}++; return 0 }
                    }
                    $fail++; return 0;
                }
            });
        }
    }
    print "    configurations by case: ",
          join('  ', map { "$_=$tally{$_}" } sort keys %tally), "\n";
    return (!$fail, "3 <= n <= $hiN, 2 <= r <= $hiR; unclassified = $fail");
  });

# ---------------------------------------------------------------- row 8
register('pair-criteria',
  'window criteria of the pair lemma agree with direct computation',
  sub {
    my ($hiN, $hiR) = $QUICK ? (9, 4) : (13, 5);
    my $bad = 0;
    for my $n (3 .. $hiN) {
        my $c = int(($n + 1) / 2);
        for my $r (2 .. $hiR) {
            my $G = stacked($n, $r);
            my $D = distances($G);
            my $mn = sub {
                my ($pts, $s) = @_;
                my $m;
                for my $p (@$pts) { my $d = $D->{$s}{$p}; $m = $d if !defined($m) || $d < $m }
                return $m;
            };
            for my $j (0 .. $r-2) {
                for my $i (0 .. $n-1) {
                    my $i2 = ($i + 1) % $n;
                    my @A  = ("v${j}_$i", "v${j}_$i2");
                    my @A1 = ("v" . ($j+1) . "_$i", "v" . ($j+1) . "_$i2");
                    my @R  = ("v${j}_$i", "v" . ($j+1) . "_$i");
                    for my $jj (0 .. $r-1) {
                        for my $k (0 .. $n-1) {
                            my $s = "v${jj}_$k";
                            my $inw = in_W($k, $i, $n, $c);
                            # (A_i^{(j)}, R_i^{(j)}) : low layers in W_i, high layers out
                            my $f1 = ($mn->(\@A,$s)  == $mn->(\@R,$s)) ? 1 : 0;
                            my $e1 = ($jj <= $j) ? $inw : (1 - $inw);
                            # (A_i^{(j+1)}, R_i^{(j)}) : roles interchanged
                            my $f2 = ($mn->(\@A1,$s) == $mn->(\@R,$s)) ? 1 : 0;
                            my $e2 = ($jj >= $j + 1) ? $inw : (1 - $inw);
                            $bad++ if $f1 != $e1 || $f2 != $e2;
                        }
                    }
                }
            }
        }
    }
    print "    mismatches between criterion and direct computation: $bad\n";
    return (!$bad, "3 <= n <= $hiN, 2 <= r <= $hiR");
  });

# ---------------------------------------------------------------- row 9
# Part (iii) of the pair lemma: the quadrilateral-face families, n even.
# Both forms are tested, including the one obtained by interchanging the
# roles of the low and high sides of the cut.
register('quad-pair-criteria',
  'quadrilateral pair criteria (part (iii)), both forms, n even',
  sub {
    my ($hiN, $hiR) = $QUICK ? (8, 3) : (14, 5);
    my $bad = 0;
    for my $n (grep { $_ % 2 == 0 } 4 .. $hiN) {
        for my $r (2 .. $hiR) {
            my $G = stacked($n, $r);
            my $D = distances($G);
            my $mn = sub {
                my ($pts, $s) = @_;
                my $m;
                for my $p (@$pts) { my $d = $D->{$s}{$p}; $m = $d if !defined($m) || $d < $m }
                return $m;
            };
            for my $j (0 .. $r-2) {
                for my $i (0 .. $n-1) {
                    my $im = ($i - 1 + $n) % $n;
                    my $ip = ($i + 1) % $n;
                    my @A  = ("v${j}_$i",         "v${j}_$ip");
                    my @A1 = ("v" . ($j+1) . "_$i", "v" . ($j+1) . "_$ip");
                    my @Q  = ("v${j}_$im", "v${j}_$i",
                              "v" . ($j+1) . "_$i", "v" . ($j+1) . "_$im");
                    for my $js (0 .. $r-1) {
                        for my $k (0 .. $n-1) {
                            my $s = "v${js}_$k";
                            my $u = ($i - $k) % $n;
                            my $zh = ($u == 0 || $u == $n/2) ? 1 : 0;
                            my $up = ($u >= $n/2 + 1) ? 1 : 0;
                            my $low = ($js <= $j) ? 1 : 0;
                            # (A_i^{(j)}, Q_i^{(j)}): low side needs u in {0,n/2}
                            my $f1 = ($mn->(\@A,  $s) == $mn->(\@Q, $s)) ? 1 : 0;
                            my $e1 = $low ? $zh : $up;
                            # (A_i^{(j+1)}, Q_i^{(j)}): the two sides interchanged
                            my $f2 = ($mn->(\@A1, $s) == $mn->(\@Q, $s)) ? 1 : 0;
                            my $e2 = $low ? $up : $zh;
                            $bad++ if $f1 != $e1 || $f2 != $e2;
                        }
                    }
                }
            }
        }
    }
    print "    mismatches between criterion and direct computation: $bad\n";
    return (!$bad, "n even, 4 <= n <= $hiN, 2 <= r <= $hiR");
  });

# ---------------------------------------------------------------- row 10
register('icosahedron',
  'MTMD(icosahedron) = 9 < 12, and F(G) is empty',
  sub {
    my $G = icosahedron();
    # sanity: 5-regular, 12 vertices, 30 edges, 20 triangular faces, Euler = 2
    my $nv = scalar @{ $G->{V} };
    my $ne = scalar @{ $G->{E} };
    my $nf = scalar @{ $G->{F} };
    my $reg = 1;
    for my $v (@{ $G->{V} }) { $reg = 0 unless scalar @{ $G->{ADJ}{$v} } == 5 }
    my $euler = ($nv - $ne + $nf == 2);
    printf "    |V|=%d |E|=%d |F|=%d  5-regular:%s  Euler:%s\n",
           $nv, $ne, $nf, ($reg ? 'yes' : 'NO'), ($euler ? 'yes' : 'NO');
    my ($forced, $viol) = forced_set_audit($G);
    my ($m, $wit) = min_resolving_size($G, 'triple');
    printf "    |F(G)|=%d  Thm 3.3 violations=%d  MTMD=%d  witness={%s}\n",
           scalar(keys %$forced), $viol, $m, join(',', @$wit);
    my $ok = $reg && $euler && $nv == 12 && $ne == 30 && $nf == 20
             && !$viol && scalar(keys %$forced) == 0 && $m == 9;
    return ($ok, 'single graph, exhaustive over all vertex subsets');
  });

# ---------------------------------------------------------------- row 10
register('bipyramid',
  'MTMD(B_n): equals |V| for n=3,4 and |V|-1 for n>=5',
  sub {
    my $hi = $QUICK ? 6 : 8;
    my $ok = 1;
    for my $n (3 .. $hi) {
        my $G = bipyramid($n);
        my ($forced, $viol) = forced_set_audit($G);
        my ($m) = min_resolving_size($G, 'triple');
        my $nv  = scalar @{ $G->{V} };
        my $expect = ($n <= 4) ? $nv : $nv - 1;
        my $good = ($m == $expect) && !$viol && (scalar(keys %$forced) >= $n);
        $ok &&= $good;
        printf "    n=%-2d |V|=%-3d MTMD=%-3d expected=%-3d |F(G)|=%-3d violations=%d\n",
               $n, $nv, $m, $expect, scalar(keys %$forced), $viol;
    }
    return ($ok, "3 <= n <= $hi");
  });

# ------------------------------------------- row 10b (Thm. on bipyramids)
register('bipyramid-theorem',
  'every step of the proof that MTMD(B_n)=n+1 for n>=5',
  sub {
    my $hi = $QUICK ? 12 : 25;
    my $bad = 0;
    my $cyc = sub { my ($a,$b,$n)=@_; my $d = abs($a-$b) % $n; $d < $n-$d ? $d : $n-$d };
    for my $n (3 .. $hi) {
        my $G = bipyramid($n);
        my $D = distances($G);

        # closed-form distances asserted in the proof
        for my $i (0 .. $n-1) {
            for my $j (0 .. $n-1) {
                my $c = $cyc->($i,$j,$n);
                my $e = $c < 2 ? $c : 2;
                $bad++ unless $D->{"c$i"}{"c$j"} == $e;
            }
            $bad++ unless $D->{"c$i"}{'N'} == 1 && $D->{"c$i"}{'S'} == 1;
        }
        $bad++ unless $D->{'N'}{'S'} == 2;

        my @C = map { "c$_" } 0 .. $n-1;
        my $els = element_list($G, 'triple');

        # lower bound: the two apices share their C-code, so C alone fails
        my $cN = join(',', map { $D->{$_}{'N'} } @C);
        my $cS = join(',', map { $D->{$_}{'S'} } @C);
        $bad++ unless $cN eq $cS;
        my ($rC) = resolves($D, \@C, $els);
        $bad++ if $rC;

        # the zero-set of the C-coordinates equals V(x) cap C, for every element
        for my $el (@$els) {
            my %inC = map { $_ => 1 } grep { /^c/ } @{ $el->[1] };
            my @z;
            for my $k (0 .. $n-1) {
                my $m;
                for my $u (@{ $el->[1] }) {
                    my $d = $D->{"c$k"}{$u}; $m = $d if !defined($m) || $d < $m }
                push @z, "c$k" if $m == 0;
            }
            $bad++ unless join(',', sort @z) eq join(',', sort keys %inC);
        }

        # the two index witnesses, existing exactly when n>=4 resp. n>=5
        my $wA = 0; for my $j (0..$n-1) { $wA = 1 if ($cyc->($j,0,$n) >= 2) }
        my $wB = 0; for my $j (0..$n-1) { $wB = 1 if ($cyc->($j,0,$n) >= 2 && $cyc->($j,1,$n) >= 2) }
        $bad++ unless $wA == ($n >= 4 ? 1 : 0);
        $bad++ unless $wB == ($n >= 5 ? 1 : 0);

        # upper bound: C u {N} resolves exactly when n>=5
        my ($rCN) = resolves($D, [@C, 'N'], $els);
        $bad++ unless $rCN == ($n >= 5 ? 1 : 0);

        printf "    n=%-3d C resolves:%-4s C+{N} resolves:%-4s witness(n>=4):%d witness(n>=5):%d\n",
               $n, ($rC ? 'yes' : 'no'), ($rCN ? 'yes' : 'no'), $wA, $wB;
    }
    return (!$bad, "3 <= n <= $hi; false claims = $bad");
  });

# ---------------------------------------------------------------- row 11
register('forcing-theorem',
  'Theorem 3.3 (containment ==> unique separator) across all test graphs',
  sub {
    my $hi = $QUICK ? 6 : 10;
    my $total_pairs = 0; my $total_viol = 0;
    my @fam;
    push @fam, [ "A_$_",     antiprism($_) ] for 3 .. $hi;
    push @fam, [ "B_$_",     bipyramid($_) ] for 3 .. $hi;
    push @fam, [ 'icosa',    icosahedron() ];
    for my $t (@fam) {
        my ($forced, $viol, $pairs) = forced_set_audit($t->[1]);
        $total_pairs += $pairs;
        $total_viol  += $viol;
        printf "    %-8s triangular (edge,face) pairs=%-4d |F(G)|=%-3d violations=%d\n",
               $t->[0], $pairs, scalar(keys %$forced), $viol;
    }
    print "    total pairs tested = $total_pairs, total violations = $total_viol\n";
    return (!$total_viol, "$total_pairs pairs");
  });

# --------------------------------- face lists include the outer face
register('faces-complete',
  "Euler's formula and face-edge incidence: no face is missing or duplicated",
  sub {
    # V - E + F = 2 fails (giving 1) if the unbounded face is omitted, and every
    # edge of a plane graph lies on exactly two faces.  Together these certify
    # that each constructor's face list is the full face set of the embedding.
    my @fam;
    push @fam, [ "Pr_$_", prism($_) ]     for (3 .. 8);
    push @fam, [ "A_$_",  antiprism($_) ] for (3 .. 8);
    push @fam, [ "B_$_",  bipyramid($_) ] for (3 .. 8);
    for my $r (2 .. 5) { push @fam, [ "C_5xP_$r", stacked(5, $r) ] }
    push @fam, [ 'icosahedron', icosahedron() ];

    my $bad = 0;
    for my $t (@fam) {
        my ($name, $G) = @$t;
        my ($v, $e, $f) = (scalar @{ $G->{V} }, scalar @{ $G->{E} }, scalar @{ $G->{F} });
        my $euler = $v - $e + $f;

        # count, for each edge, how many faces have it on their boundary cycle
        my %cnt;
        for my $F (@{ $G->{F} }) {
            my @c = @$F;
            for my $i (0 .. $#c) {
                my $key = join('|', sort ($c[$i], $c[($i + 1) % @c]));
                $cnt{$key}++;
            }
        }
        my ($on2, $tot) = (0, 0);
        for my $E (@{ $G->{E} }) {
            $tot++;
            $on2++ if ($cnt{ join('|', sort @$E) } // 0) == 2;
        }
        $bad++ unless $euler == 2 && $on2 == $tot;
        printf "    %-12s |V|=%-3d |E|=%-3d |F|=%-3d  V-E+F=%-2d  edges on exactly 2 faces: %d/%d\n",
               $name, $v, $e, $f, $euler, $on2, $tot;
    }
    return (!$bad, scalar(@fam) . " graphs; failures = $bad");
  });

# ------------------------------------- trivial lower bound MTMD >= 3
register('lower-bound-3',
  'no 1- or 2-element set resolves a 2-connected plane graph',
  sub {
    # K_{2,3}, theta(2,2,3) and K_4 are the smallest 2-connected plane graphs
    # whose distinct faces have distinct vertex sets; add the small prisms.
    my @fam;
    push @fam, [ 'K_{2,3}',
        mk_graph([qw(x y a b c)],
                 [[qw(x a)],[qw(a y)],[qw(x b)],[qw(b y)],[qw(x c)],[qw(c y)]],
                 [[qw(x a y b)],[qw(x b y c)],[qw(x a y c)]]) ];
    push @fam, [ 'theta(2,2,3)',
        mk_graph([qw(x y a b c d)],
                 [[qw(x a)],[qw(a y)],[qw(x b)],[qw(b y)],[qw(x c)],[qw(c d)],[qw(d y)]],
                 [[qw(x a y b)],[qw(x b y d c)],[qw(x a y d c)]]) ];
    push @fam, [ 'K_4',
        mk_graph([qw(1 2 3 4)],
                 [[qw(1 2)],[qw(1 3)],[qw(1 4)],[qw(2 3)],[qw(2 4)],[qw(3 4)]],
                 [[qw(1 2 3)],[qw(1 2 4)],[qw(1 3 4)],[qw(2 3 4)]]) ];
    push @fam, [ "Pr_$_", prism($_) ]     for (3, 4, 5);
    push @fam, [ "A_$_",  antiprism($_) ] for (3, 4);
    push @fam, [ "B_$_",  bipyramid($_) ] for (3, 4, 5);

    my $ok = 1;
    for my $t (@fam) {
        my ($name, $G) = @$t;
        my $mind = 1e9;
        for my $v (@{ $G->{V} }) {
            my $d = scalar @{ $G->{ADJ}{$v} };
            $mind = $d if $d < $mind;
        }
        # verify directly that no subset of size 1 or 2 resolves
        my ($none) = no_resolving_below($G, 'triple', 3);
        my ($m)    = min_resolving_size($G, 'triple');
        my $good = $none && $m >= 3 && $mind >= 2;
        $ok &&= $good;
        printf "    %-13s |V|=%-3d min-deg=%-2d  no 1- or 2-set resolves: %-4s MTMD=%d\n",
               $name, scalar @{ $G->{V} }, $mind, ($none ? 'yes' : 'NO'), $m;
    }
    return ($ok, scalar(@fam) . ' graphs');
  });

# ------------------------------------------------- row 13 (Prop. on A_4)
register('A4-anomaly',
  'every step of the proof that mmd(A_4)=5',
  sub {
    # A_n = C_{2n}(1,2) with d(s,t) = ceil(Delta/2); a_i -> 2i, b_i -> 2i+1
    my $del  = sub { my ($a,$b,$N)=@_; my $d = abs($a-$b) % $N; $d < $N-$d ? $d : $N-$d };
    my $dist = sub { my ($a,$b,$N)=@_; int(($del->($a,$b,$N) + 1) / 2) };
    my $bad = 0;

    # Step 1: diam(A_n) = ceil(n/2), so diam(A_4)=2 and diam(A_n)>=3 for n>=5
    for my $n (3 .. 12) {
        my $N = 2 * $n; my $dm = 0;
        for my $t (0 .. $N-1) { my $d = $dist->(0,$t,$N); $dm = $d if $d > $dm }
        $bad++ unless $dm == int(($n + 1) / 2);
    }
    print "    diam(A_n) = ceil(n/2) for 3<=n<=12: ", ($bad ? 'FAIL' : 'verified'), "\n";

    # Step 2: separator set of (v_0, v_0v_1) is {1,3} in A_4, {1,3,5} for n=5,6
    my %expect_sep = (4 => '1,3', 5 => '1,3,5', 6 => '1,3,5');
    for my $n (4, 5, 6) {
        my $N = 2 * $n;
        my @sep = grep { $dist->($_,1,$N) < $dist->($_,0,$N) } 0 .. $N-1;
        my $got = join(',', @sep);
        printf "    n=%d separators of (v_0, v_0v_1) = {%s}\n", $n, $got;
        $bad++ unless $got eq $expect_sep{$n};
    }

    # Step 3: exactly four 4-subsets of Z_8 meet {v+1,v+3} and {v-1,v-3} for all v
    my $N = 8;
    my @conds;
    for my $v (0 .. $N-1) {
        push @conds, [ grep { $dist->($_,($v+1)%$N,$N) < $dist->($_,$v,$N) } 0..$N-1 ];
        push @conds, [ grep { $dist->($_,($v-1+$N)%$N,$N) < $dist->($_,$v,$N) } 0..$N-1 ];
    }
    my @survive;
    each_subset($N, 4, sub {
        my ($idx) = @_;
        my %in = map { $_ => 1 } @$idx;
        for my $c (@conds) {
            my $hit = 0; for my $x (@$c) { $hit = 1 if $in{$x} }
            return 0 unless $hit;
        }
        push @survive, [ @$idx ];
        return 0;
    });
    print "    4-subsets surviving the covering conditions: ",
          join('  ', map { '{' . join(',', @$_) . '}' } @survive), "\n";
    $bad++ unless @survive == 4;

    # each survivor is invariant under the antipodal map t -> t+4
    for my $T (@survive) {
        my %in = map { $_ => 1 } @$T;
        for my $s (@$T) { $bad++ unless $in{ ($s + 4) % $N } }
    }

    # Step 4: each survivor leaves a pair of diagonals with equal all-ones code
    my %adj;
    for my $t (0 .. $N-1) { for my $k (1,2) {
        $adj{$t}{($t+$k)%$N} = 1; $adj{($t+$k)%$N}{$t} = 1 } }
    my @E;
    for my $a (0 .. $N-1) { for my $b ($a+1 .. $N-1) { push @E, [$a,$b] if $adj{$a}{$b} } }
    for my $T (@survive) {
        my (%seen, @coll);
        for my $e (@E) {
            my @c;
            for my $s (@$T) {
                my $m;
                for my $u (@$e) { my $d = $dist->($s,$u,$N); $m = $d if !defined($m) || $d < $m }
                push @c, $m;
            }
            my $k = join(',', @c);
            push @coll, "{$e->[0],$e->[1]} vs {" . join(',', @{$seen{$k}}) . "} code=($k)"
                if exists $seen{$k};
            $seen{$k} //= $e;
        }
        printf "    S={%s} unresolved edge pair: %s\n",
               join(',', @$T), (@coll ? $coll[0] : '*** NONE -- RESOLVES ***');
        $bad++ unless @coll;
    }

    # the stated witness of size 5 really works, on V u E
    my $G  = antiprism(4);
    my @W  = ('a0','b0','a1','b2','a3');
    my ($ok5) = resolves(distances($G), \@W, element_list($G, 'mixed'));
    print "    witness {a0,b0,a1,b2,a3} mixed-resolves A_4: ", ($ok5 ? 'yes' : 'NO'), "\n";
    $bad++ unless $ok5;

    # Where the published construction degenerates.  Raza, Liu and Qu obtain
    # mmd(A_n) <= 4 for even n = 2m from the candidate generator
    #     L_m = { y_0, y_m, x_2, x_{m+2} }        (y = outer, x = inner).
    # The outer indices are {0,m} and the inner ones {2,m+2}.  These pairs are
    # distinct for n >= 6 but coincide at n = 4, where L_m becomes invariant
    # under the antipodal rotation and cannot separate the two diagonals.
    for my $n (4, 6, 8, 10, 12) {
        my $m  = $n / 2;
        my $G4 = antiprism($n);
        my $D4 = distances($G4);
        my $el = element_list($G4, 'mixed');
        my @L  = ("a0", "a$m", "b2", "b" . (($m + 2) % $n));
        my ($ok, $x, $y) = resolves($D4, \@L, $el);
        my $samepair = (join(',', sort (0, $m)) eq join(',', sort (2, ($m+2) % $n))) ? 1 : 0;
        printf "    n=%-3d L_m={y0,y%d,x2,x%d} index pairs coincide: %-3s resolves: %s\n",
               $n, $m, ($m + 2) % $n, ($samepair ? 'yes' : 'no'), ($ok ? 'yes' : 'no');
        # index-pair coincidence happens only at n=4
        $bad++ if $samepair != ($n == 4);
        $bad++ if $n == 4 && $ok;           # L_m must fail at n=4
        $bad++ if $n == 6 && $ok;           # and, as noted in the text, at n=6
        $bad++ if $n >= 8 && !$ok;          # but must succeed from n=8 on
    }
    # At n=6 the generator fails yet the stated value 4 is still correct,
    # attained by another 4-set; at n=4 no 4-set exists at all.
    my ($m6) = min_resolving_size(antiprism(6), 'mixed');
    my ($ok6) = resolves(distances(antiprism(6)),
                         ['a0','b1','a3','b4'], element_list(antiprism(6), 'mixed'));
    printf "    mmd(A_6)=%d with witness {a0,b1,a3,b4} resolving: %s\n",
           $m6, ($ok6 ? 'yes' : 'no');
    $bad++ unless $m6 == 4 && $ok6;

    return (!$bad, "all steps of Proposition on mmd(A_4); false claims = $bad");
  });

# ---------------------------------------------------------------- row 12
register('layered-family',
  'MTMD(L(n,r,sigma)) against the conjectured values, including the n=3 exception',
  sub {
    # L(n,r,sigma): strip j+1 joins layer j to layer j+1.
    # Q -> rungs only; T -> rungs plus the diagonals lo_{i+1}--hi_i.
    my $build = sub {
        my ($n, $sig) = @_;
        my $r = length($sig) + 1;
        my $id = sub { my ($j,$i) = @_; "v${j}_" . ((($i % $n) + $n) % $n) };
        my (@V, @E, @F);
        for my $j (0 .. $r-1) { push @V, $id->($j,$_) for 0 .. $n-1 }
        for my $j (0 .. $r-1) { push @E, [$id->($j,$_), $id->($j,$_+1)] for 0 .. $n-1 }
        for my $j (0 .. $r-2) {
            push @E, [$id->($j,$_), $id->($j+1,$_)] for 0 .. $n-1;
            if (substr($sig, $j, 1) eq 'T') {
                push @E, [$id->($j,$_+1), $id->($j+1,$_)] for 0 .. $n-1;
                for my $i (0 .. $n-1) {
                    push @F, [$id->($j,$i),   $id->($j,$i+1),   $id->($j+1,$i)];
                    push @F, [$id->($j+1,$i), $id->($j+1,$i+1), $id->($j,$i+1)];
                }
            } else {
                for my $i (0 .. $n-1) {
                    push @F, [$id->($j,$i), $id->($j,$i+1),
                              $id->($j+1,$i+1), $id->($j+1,$i)];
                }
            }
        }
        push @F, [ map { $id->(0,$_) } 0 .. $n-1 ];
        push @F, [ map { $id->($r-1,$_) } 0 .. $n-1 ];
        return mk_graph(\@V, \@E, \@F);
    };
    my @cases = $QUICK
      ? ([3,'T'],[3,'TT'],[4,'QT'],[4,'TT'])
      : ([3,'Q'],[4,'Q'],[5,'Q'],[3,'T'],[4,'T'],[5,'T'],[6,'T'],
         [3,'QQ'],[4,'QQ'],[3,'QT'],[3,'TQ'],[3,'TT'],
         [4,'QT'],[4,'TQ'],[4,'TT'],[5,'QT'],[5,'TT'],[6,'TT'],
         [3,'QQQ'],[3,'QQT'],[3,'QTQ'],[3,'TQQ'],[3,'QTT'],[3,'TQT'],
         [3,'TTQ'],[3,'TTT'],
         [4,'QQT'],[4,'QTQ'],[4,'TQQ'],[4,'TTT'],
         [3,'QQTT'],[3,'TQQT'],[3,'QTTT'],[3,'TTTT'],
         # QTTQ is the decisive case for Remark rem:n3: t=2, no extreme
         # T-strip, hence F(G) empty, yet the value is 2t+4 = 8 > 2n = 6.
         # It shows the n=3 growth is NOT produced by the forcing criterion.
         [3,'QTTQ']);
    # For each graph, precompute ED[s][x] = d(s, element x) once; then a
    # candidate test is |elements| * |S| array reads.  By monotonicity (any
    # superset of a resolving set resolves) it suffices to check that some
    # set of size m resolves and that no set of size m-1 does.
    my $probe = sub {
        my ($G, $k) = @_;
        my $D   = distances($G);
        my $els = element_list($G, 'triple');
        my $V   = $G->{V};
        my $N   = scalar @$V;
        my @ED;
        for my $si (0 .. $N-1) {
            my $ds = $D->{ $V->[$si] };
            $ED[$si] = [ map { my $m; for my $u (@{$_->[1]}) {
                                   $m = $ds->{$u} if !defined($m) || $ds->{$u} < $m }
                               $m } @$els ];
        }
        my $ne = scalar @$els;
        my @idx = (0 .. $k-1);
        while (1) {
            my @rows = map { $ED[$_] } @idx;
            my (%seen, $clash);
            for my $x (0 .. $ne-1) {
                my $key = join ',', map { $_->[$x] } @rows;
                if ($seen{$key}++) { $clash = 1; last }
            }
            return [ map { $V->[$_] } @idx ] unless $clash;
            my $i = $k - 1;
            $i-- while $i >= 0 && $idx[$i] == $N - $k + $i;
            last if $i < 0;
            $idx[$i]++;
            $idx[$_] = $idx[$_-1] + 1 for $i+1 .. $k-1;
        }
        return undef;
    };
    my $bad = 0;
    for my $c (@cases) {
        my ($n, $sig) = @$c;
        my $r = length($sig) + 1;
        my $t = ($sig =~ tr/T//);
        my $G = $build->($n, $sig);
        my $exp = ($t == 0) ? 4 : (($n >= 4) ? 2*$n : 2*$t + 4);
        my $up  = $probe->($G, $exp);
        my $low = $probe->($G, $exp - 1);
        my $ok  = ($up && !$low) ? 1 : 0;
        $bad++ unless $ok;
        printf "    L(%d,%d,%-5s) |V|=%-3d t=%d  expected %-3d  %s\n",
               $n, $r, $sig, scalar @{$G->{V}}, $t, $exp,
               $ok ? "confirmed (some $exp-set resolves, no " . ($exp-1) . "-set does)"
                   : ($low ? "<-- MISMATCH: a " . ($exp-1) . "-set resolves"
                           : "<-- MISMATCH: no $exp-set resolves");
    }
    print "    mismatches: $bad\n";
    return (!$bad, scalar(@cases) . " strip words, 3 <= n <= 6, 2 <= r <= 5, |V| <= 18");
  });

# ---------------------------------------------------------------- row 17
# Theorem thm:deleteone / Corollary cor:extremal.  For each vertex v the
# predicate "v is neither dominated nor critical" is compared against the
# ground truth "V \ {v} is a mixed triple resolving set".
register('delete-one',
  'V minus one vertex resolves iff that vertex is neither dominated nor critical',
  sub {
    my $hi = $QUICK ? 6 : 9;
    my ($bad, $verts, $graphs) = (0, 0, 0);

    my $analyse = sub {
        my ($G, $name) = @_;
        my $D   = distances($G);
        my @V   = @{ $G->{V} };
        my %adj = map { my $x = $_; ($x => { map { $_ => 1 } @{ $G->{ADJ}{$x} } }) } @V;
        my %isedge;
        for my $e (@{ $G->{E} }) { my ($a,$b) = @$e;
            $isedge{ $a lt $b ? "$a|$b" : "$b|$a" } = 1 }
        my $els = element_list($G, 'triple');
        my $free = 0;
        for my $v (@V) {
            my $dominated = 0;
            for my $u (@{ $G->{ADJ}{$v} }) {
                my $sub = 1;
                for my $w (@{ $G->{ADJ}{$v} }) {
                    next if $w eq $u;
                    unless ($adj{$u}{$w}) { $sub = 0; last }
                }
                if ($sub) { $dominated = 1; last }
            }
            my $critical = 0;
            for my $f (@{ $G->{F} }) {
                next unless @$f == 3;
                next unless grep { $_ eq $v } @$f;
                my ($u, $w) = grep { $_ ne $v } @$f;
                next unless $isedge{ $u lt $w ? "$u|$w" : "$w|$u" };
                my @sep = grep { $D->{$_}{$u} == $D->{$_}{$w}
                              && $D->{$_}{$u} == $D->{$_}{$v} + 1 } @V;
                if (@sep == 1 && $sep[0] eq $v) { $critical = 1; last }
            }
            my @S = grep { $_ ne $v } @V;
            my ($ok) = resolves($D, \@S, $els);
            my $pred = (!$dominated && !$critical) ? 1 : 0;
            $bad++ if ($ok ? 1 : 0) != $pred;
            $free++ if $pred;
            $verts++;
        }
        $graphs++;
        return $free;
    };

    for my $n (3 .. $hi) {
        my $fa = $analyse->(antiprism($n), "A_$n");
        my $fb = $analyse->(bipyramid($n), "B_$n");
        $analyse->(prism($n), "Pr_$n");
        # A_n is extremal: no vertex may be deleted.  B_n for n >= 5 has
        # exactly the two apices free, and dim_m^t = |V| - 1 there.
        $bad++ if $fa != 0;
        $bad++ if $n >= 5 && $fb != 2;
        $bad++ if $n <= 4 && $fb != 0;
        printf "    n=%-3d free vertices: A_n=%-3d B_n=%-3d\n", $n, $fa, $fb;
    }
    my $fi = $analyse->(icosahedron(), 'icosahedron');
    for my $n (3 .. 6) { for my $r (2 .. 4) { $analyse->(stacked($n,$r), "C${n}xP$r") } }
    printf "    icosahedron free vertices: %d of 12\n", $fi;
    $bad++ unless $fi == 12;

    print "    graphs=$graphs vertices tested=$verts\n";
    return (!$bad, "$graphs graphs, $verts vertices; mismatches = $bad");
  });

# ---------------------------------------------------------------- row 18
# The dim_f column of the comparison table, and the reduction of
# Proposition prop:fmd-antiprism: for |K| = 3, a set of top-layer vertices
# face-resolves A_n exactly when K mixed-resolves the cycle C_n.
register('face-dimension',
  'dim_f column of the comparison table, and the antiprism reduction',
  sub {
    my ($hi, $hiCyc) = $QUICK ? (8, 8) : (14, 12);
    my $bad = 0;

    # minimum face-resolving set size
    # each_subset takes the SIZE of the ground set and hands the callback a
    # list of indices; the callback returns true to stop the scan.
    my $facedim = sub {
        my ($G) = @_;
        my @V = @{ $G->{V} };
        my $D = distances($G);
        my $F = $G->{F};
        for my $k (1 .. scalar @V) {
            my $hit = 0;
            each_subset(scalar @V, $k, sub {
                my ($idx) = @_;
                my @S = @V[ @$idx ];
                my %seen;
                for my $f (@$F) { return 0 if $seen{ elem_code($D, \@S, $f) }++ }
                $hit = 1;
                return 1;                       # resolving set found: stop
            });
            return $k if $hit;
        }
        return undef;
    };

    for my $n (3 .. $hi) {
        my $p = $facedim->(prism($n));
        my $a = $facedim->(antiprism($n));
        my $ep = ($n <= 5) ? 3 : 2;
        $bad++ if $p != $ep || $a != 3;
        printf "    n=%-3d dim_f(Pr_n)=%-2d (exp %d)  dim_f(A_n)=%-2d (exp 3)\n",
               $n, $p, $ep, $a;
    }
    for my $n (3 .. ($QUICK ? 6 : 9)) {
        my $m = $facedim->(stacked($n, 3));
        $bad++ if $m != 3;
    }
    print "    dim_f(M_n)=3 for every n tested\n";

    my $ic = $facedim->(icosahedron());
    my ($icm) = min_resolving_size(icosahedron(), 'mixed');
    printf "    icosahedron: dim_f=%d (exp 5)  dim_m=%d (exp 6)\n", $ic, $icm;
    $bad++ if $ic != 5 || $icm != 6;

    # bipyramids: dim_m and dim_m^t coincide at |V|-1 for n >= 5, and every
    # step of the lower-bound proof of Proposition prop:bipyramid-free.
    for my $n (3 .. ($QUICK ? 6 : 10)) {
        my $G  = bipyramid($n);
        my $D  = distances($G);
        my $V  = scalar @{ $G->{V} };
        my $me = element_list($G, 'mixed');

        # (i) the separators of (N, N c_0) are exactly {c_0, S}
        my @sep = grep { $D->{$_}{'c0'} < $D->{$_}{'N'} } @{ $G->{V} };
        my $sep_ok = join(',', sort @sep) eq join(',', sort ('S','c0'));

        # (ii) the n cycle vertices alone fail, because N and S collide
        my @cyc = map { "c$_" } 0 .. $n-1;
        my $ns_collide =
            (elem_code($D, \@cyc, ['N']) eq elem_code($D, \@cyc, ['S'])) ? 1 : 0;

        # (iii) with N,S in and two cycle vertices out, N c_p and N c_q collide
        my @R = ('N', 'S', map { "c$_" } 2 .. $n-1);
        my $edge_collide =
            (elem_code($D, \@R, ['c0','N']) eq elem_code($D, \@R, ['c1','N'])) ? 1 : 0;

        # (iv) the diameter is 2
        my $diam = 0;
        for my $a (@{$G->{V}}) { for my $b (@{$G->{V}}) {
            $diam = $D->{$a}{$b} if $D->{$a}{$b} > $diam } }

        my ($m) = min_resolving_size($G, 'mixed');
        printf "    B_%-2d |V|=%-3d diam=%d dim_m=%-3d (>= n+1 = %d)  sep(N,Nc0)={%s}\n",
               $n, $V, $diam, $m, $n+1, join(',', sort @sep);
        $bad++ unless $sep_ok && $ns_collide && $edge_collide && $diam == 2 && $m >= $n+1;

        if ($n >= 5) {
            my ($t) = min_resolving_size($G, 'triple');
            $bad++ unless $m == $t && $t == $V - 1;
        }
    }

    # the reduction: |K|=3 face-resolves A_n  <=>  K mixed-resolves C_n
    my $cycle_mixed = sub {
        my ($n, $K) = @_;
        my %seen;
        for my $v (0 .. $n-1) { return 0 if $seen{ join ',', map { cyc($_,$v,$n) } @$K }++ }
        for my $i (0 .. $n-1) { return 0 if $seen{ join ',', map { mu($_,$i,$n) } @$K }++ }
        return 1;
    };
    my $pairs = 0;
    for my $n (3 .. $hiCyc) {
        my $G = antiprism($n); my $D = distances($G);
        for my $x (0 .. $n-1) { for my $y ($x+1 .. $n-1) { for my $z ($y+1 .. $n-1) {
            my @K = ($x, $y, $z);
            my @S = map { "a$_" } @K;
            my %seen; my $fr = 1;
            for my $f (@{ $G->{F} }) { if ($seen{ elem_code($D, \@S, $f) }++) { $fr = 0; last } }
            my $cm = $cycle_mixed->($n, \@K);
            $bad++ if $fr != $cm;
            $pairs++;
        }}}
    }
    printf "    reduction to C_n verified on %d triples, 3 <= n <= %d\n", $pairs, $hiCyc;

    return (!$bad, "dim_f for 3 <= n <= $hi; reduction for 3 <= n <= $hiCyc; failures = $bad");
  });

# ---------------------------------------------------------------- row 18
register('mmd-values',
  'mmd values quoted in the comparison table',
  sub {
    my ($lo, $hi) = $QUICK ? (3, 7) : (3, 11);
    my $ok = 1;
    for my $n ($lo .. $hi) {
        my ($mp) = min_resolving_size(prism($n),     'mixed');
        my ($ma) = min_resolving_size(antiprism($n), 'mixed');
        my ($mm) = min_resolving_size(stacked($n,3), 'mixed');
        # Expected values.  mmd(Pr_n) = 3 (n even), 4 (n odd).
        # mmd(A_n) = 4 (n even), 5 (n odd), with the single exception n=4,
        # where exhaustive search over all 4-subsets returns none, so
        # mmd(A_4) = 5.  Note n=3 is NOT an exception: diam(A_3)=2 as well,
        # so the same scarcity occurs, but the odd case already predicts 5.
        my $ep = ($n % 2 == 0) ? 3 : 4;
        my $ea = ($n == 4) ? 5 : (($n % 2 == 0) ? 4 : 5);
        my $good = ($mp == $ep) && ($ma == $ea);
        $ok &&= $good;
        printf "    n=%-2d mmd(Pr_n)=%d (exp %d)  mmd(A_n)=%d (exp %d)  mmd(M_n)=%d\n",
               $n, $mp, $ep, $ma, $ea, $mm;
    }
    return ($ok, "$lo <= n <= $hi");
  });

# =====================================================================
#  MAIN
# =====================================================================

print "=" x 72, "\n";
print "MTMD verification suite", ($QUICK ? "  [--quick: reduced ranges]" : ""), "\n";
print "=" x 72, "\n";

my $ran = 0;
for my $c (@CHECKS) {
    my ($name, $desc, $code) = @$c;
    next if $ONLY && $name ne $ONLY;
    $ran++;
    print "\n$name -- $desc\n";
    my ($ok, $detail) = $code->();
    report($name, $ok, $detail);
}

die "no check matched --only=$ONLY\n" unless $ran;

print "\n", "=" x 72, "\n";
if ($FAILURES) { print "RESULT: $FAILURES check(s) FAILED\n"; exit 1 }
print "RESULT: all $ran check(s) passed\n";
exit 0;
