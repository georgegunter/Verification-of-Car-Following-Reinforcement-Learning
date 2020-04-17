#!/usr/bin/perl -w
#Input: any number of logfiles.
#Output: (1) A list of solved problems with minumum proof times
#        (2) A count of problems solved significantly faster
#              (by some given margin or factor) than in any other logfile.

use strict;
use Getopt::Long;

my $margin=5;  #minimum difference in processor time regarded as significant
my $factor=1;  #minimum ratio in processor times regarded as significant
GetOptions ('margin=i' => \$margin, 'factor=f' => \$factor)
  or die "usage: [--margin=i] [--factor=f] <files>\n";

#We don't use both a factor and a margin.
unless ($factor==1) {
  $margin=0;
  die "factor must exceed 1.0" if ($factor <= 1);
}

my (%min_time, %best_file, %num_proofs);

sub too_close {
  my ($x, $y) = @_;
  $factor == 1 ? abs ($x - $y) < $margin :
  $x > $y     ? $x < $factor*$y : $y < $factor*$x;
}

foreach my $logfile (@ARGV) {
  my (@pathcomps)=split(/\//, $logfile);   #components of pathname: last is filename
  my (@fnamecomps)=split(/\./, $pathcomps[-1]);
  pop (@fnamecomps);                       #delete filename extension
  my ($logname)=join(".", @fnamecomps);    #rebuild filename (including other full stops)
  open LOG, "$logfile" or die "Can't open file $logfile: $!";
  while (<LOG>) {
    my ($probname,$cputime) = /([^;\s]+); proved; *([\d.]+) seconds/;
    next if (not (defined($probname)));
    if (exists $num_proofs{$probname}) {
      $num_proofs{$probname}++;
      if (too_close ($min_time{$probname}, $cputime)) { #difference NOT significant
        $best_file{$probname} = undef;
        $min_time{$probname} = $cputime if ($cputime < $min_time{$probname});
      } else {
        if ($cputime < $min_time{$probname}) {  #note new significant proof
          $best_file{$probname} = $logname;
          $min_time{$probname} = $cputime;
        }
      }
    } else {   #FIRST proof for this problem
      $num_proofs{$probname} = 1;
      $best_file{$probname} = $logname;
      $min_time{$probname} = $cputime;
    }
  }
  close LOG;
}

##MINIMUM RUNTIMES AND BEST LOGFILES
my %num_best;

print "\nProblem; minumum runtimes [number of proofs], ID of best proof\n";
foreach my $probname (sort {lc $a cmp lc $b} keys %num_proofs) {
  print $probname, ";";
  printf "%7.1f seconds", $min_time{$probname};
  print " [$num_proofs{$probname}]";
  if (defined $best_file{$probname}) {
    print ", $best_file{$probname}";
    $num_best{$best_file{$probname}} = 1 +
      (exists $num_best{$best_file{$probname}} ? $num_best{$best_file{$probname}} : 0);
  }
  print "\n";
}

my $nproblems=0;  #total number of problems

##FINAL SUMMARY STATISTICS

print STDOUT "\nNumber of Fastest or Unique Proofs by Log File";
if ($factor == 1) {
  print STDOUT " (margin = $margin)\n";
} else {
  print STDOUT " (factor = $factor)\n";
}
foreach my $logfile (sort {lc $a cmp lc $b} keys %num_best) {
  printf "%4u: ", $num_best{$logfile};
  print $logfile, "\n";
}


