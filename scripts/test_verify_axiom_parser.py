#!/usr/bin/env python3
"""Regression checks for declaration names in Lean's axiom reports."""

import unittest

from verify import parse_axiom_reports


class AxiomReportParserTests(unittest.TestCase):
    def test_complete_names(self):
        names = ["Example.ordinary", "Example.terminal'", "Example.inner'.value",
                 "Example.inner'.terminal''"]
        for name in names:
            with self.subTest(name=name):
                self.assertEqual(parse_axiom_reports(
                    f"'{name}' depends on axioms: [propext, Quot.sound, Classical.choice]\n"),
                    {name: ["Classical.choice", "Quot.sound", "propext"]})
                self.assertEqual(parse_axiom_reports(
                    f"'{name}' does not depend on any axioms\n"), {name: []})

    def test_names_do_not_collide(self):
        text = ("Current module: Example\n"
                "'Example.value' depends on axioms: [propext]\n"
                "'Example.value'' does not depend on any axioms\n"
                "'Example.inner'.value' depends on axioms: [Quot.sound]\n")
        self.assertEqual(parse_axiom_reports(text), {
            "Example.value": ["propext"], "Example.value'": [],
            "Example.inner'.value": ["Quot.sound"]})

    def test_unexpected_axioms_are_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "Unexpected axioms in Example.bad'"):
            parse_axiom_reports("'Example.bad'' depends on axioms: [sorryAx]\n")

    def test_unparsed_report_is_rejected(self):
        for text in ["'Example.bad' depends on axioms: malformed\n",
                     "'Example.bad' does not depend on any axioms [sorryAx]\n"]:
            with self.subTest(text=text), self.assertRaisesRegex(
                    RuntimeError, "missing, truncated, or repeated"):
                parse_axiom_reports(text)

    def test_duplicate_report_is_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "missing, truncated, or repeated"):
            parse_axiom_reports("'Example.duplicate' does not depend on any axioms\n" * 2)


if __name__ == "__main__":
    unittest.main()
