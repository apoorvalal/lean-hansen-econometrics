from __future__ import annotations

from manim import *


config.background_color = "#101216"
config.frame_width = 16
config.frame_height = 9
config.pixel_width = 1920
config.pixel_height = 1080


TEXT = "#F2F0EA"
MUTED = "#B7B3AA"
BLUE = "#4EA5D9"
GREEN = "#63B36D"
GOLD = "#D6A94A"
RED = "#D66A5E"
PURPLE = "#9B7EDE"
PANEL = "#1A1F27"
GRID = "#303744"


class FWLStructure(Scene):
    """Animated proof map for HansenEconometrics.Chapter3FWL."""

    def construct(self) -> None:
        self.camera.background_color = "#101216"
        self.intro()
        self.full_regression()
        self.partial_out_x1()
        self.auxiliary_regression()
        self.coefficient_identity()
        self.residual_and_sequential_maker()
        self.dependency_map()
        self.outro()

    def title(self, text: str, subtitle: str | None = None) -> VGroup:
        head = Text(text, font_size=34, weight=BOLD, color=TEXT)
        head.to_edge(UP, buff=0.28)
        if subtitle is None:
            return VGroup(head)
        sub = Text(subtitle, font_size=18, color=MUTED)
        sub.next_to(head, DOWN, buff=0.08)
        return VGroup(head, sub)

    def card(self, title: str, body: Mobject, color: str = BLUE, width: float = 4.7) -> VGroup:
        title_mob = Text(title, font_size=22, weight=BOLD, color=TEXT)
        title_mob.set_color(color)
        body.scale_to_fit_width(width - 0.45)
        content = VGroup(title_mob, body).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        box = RoundedRectangle(
            corner_radius=0.08,
            width=max(width, content.width + 0.5),
            height=content.height + 0.42,
            stroke_color=color,
            stroke_width=1.6,
            fill_color=PANEL,
            fill_opacity=0.92,
        )
        content.move_to(box.get_center())
        return VGroup(box, content)

    def formula(self, tex: str, font_size: int = 34, color: str = TEXT) -> MathTex:
        mob = MathTex(tex, font_size=font_size, color=color)
        return mob

    def label(self, text: str, font_size: int = 24, color: str = TEXT) -> Text:
        return Text(text, font_size=font_size, color=color)

    def theorem_node(
        self,
        name: str,
        summary: str,
        color: str = BLUE,
        width: float = 3.55,
    ) -> VGroup:
        name_mob = Text(name, font_size=15, weight=BOLD, color=color)
        if name_mob.width > width - 0.28:
            name_mob.scale_to_fit_width(width - 0.28)
        summary_mob = Text(summary, font_size=13, color=TEXT)
        if summary_mob.width > width - 0.28:
            summary_mob.scale_to_fit_width(width - 0.28)
        group = VGroup(name_mob, summary_mob).arrange(DOWN, buff=0.08)
        box = RoundedRectangle(
            corner_radius=0.06,
            width=width,
            height=max(0.72, group.height + 0.24),
            stroke_color=color,
            stroke_width=1.2,
            fill_color=PANEL,
            fill_opacity=0.96,
        )
        group.move_to(box)
        return VGroup(box, group)

    def intro(self) -> None:
        title = Text("Frisch-Waugh-Lovell in Lean", font_size=46, weight=BOLD, color=TEXT)
        title.to_edge(UP, buff=0.7)
        file_name = Text("HansenEconometrics/Chapter3FWL.lean", font_size=24, color=MUTED)
        file_name.next_to(title, DOWN, buff=0.18)

        left = self.card(
            "Full regression target",
            self.formula(r"\hat\beta_2([X_1\;X_2],y)", font_size=32),
            BLUE,
            width=5.1,
        )
        right = self.card(
            "Residualized regression target",
            self.formula(r"\hat\beta(M_1X_2,M_1y)", font_size=32),
            GREEN,
            width=5.1,
        )
        left.shift(LEFT * 3.0 + DOWN * 0.3)
        right.shift(RIGHT * 3.0 + DOWN * 0.3)

        equal = self.formula(r"=", font_size=58, color=GOLD)
        equal.move_to(ORIGIN + DOWN * 0.3)

        residual = self.card(
            "Residuals also match",
            self.formula(r"\hat e_{FWL}=\hat e_{full}", font_size=34),
            GOLD,
            width=5.4,
        )
        residual.to_edge(DOWN, buff=0.75)

        self.play(FadeIn(title, shift=DOWN), FadeIn(file_name, shift=DOWN))
        self.play(FadeIn(left, shift=RIGHT), FadeIn(right, shift=LEFT), Write(equal))
        self.play(FadeIn(residual, shift=UP))
        self.wait(1.0)
        self.play(FadeOut(VGroup(title, file_name, left, right, equal, residual)))

    def full_regression(self) -> None:
        title = self.title(
            "Step 1: split the full normal equations",
            "Lean starts with the OLS residual from the column-partitioned design.",
        )
        design = self.formula(
            r"X=\operatorname{fromCols}(X_1,X_2),\qquad"
            r"\hat e=y-X\hat\beta",
            font_size=34,
        )
        design.next_to(title, DOWN, buff=0.48)

        matrix = VGroup(
            Rectangle(width=1.45, height=3.4, fill_color=BLUE, fill_opacity=0.75, stroke_color=BLUE),
            Rectangle(width=1.45, height=3.4, fill_color=GREEN, fill_opacity=0.75, stroke_color=GREEN),
        ).arrange(RIGHT, buff=0.08)
        matrix.shift(LEFT * 4.65 + DOWN * 0.35)
        x1 = Text("X1", font_size=30, weight=BOLD, color="#101216").move_to(matrix[0])
        x2 = Text("X2", font_size=30, weight=BOLD, color="#101216").move_to(matrix[1])
        matrix_group = VGroup(matrix, x1, x2)
        bracket_label = Text("fromCols X1 X2", font_size=20, color=MUTED)
        bracket_label.next_to(matrix_group, DOWN, buff=0.22)

        full_ne = self.card(
            "normal_equations",
            self.formula(r"X^T\hat e=0", font_size=38),
            GOLD,
            width=3.6,
        )
        full_ne.shift(LEFT * 0.2 + DOWN * 0.35)

        left_ne = self.card(
            "normal_equations_fromCols_left",
            self.formula(r"X_1^T\hat e=0", font_size=34),
            BLUE,
            width=4.7,
        )
        right_ne = self.card(
            "normal_equations_fromCols_right",
            self.formula(r"X_2^T\hat e=0", font_size=34),
            GREEN,
            width=4.7,
        )
        split = VGroup(left_ne, right_ne).arrange(DOWN, buff=0.35)
        split.shift(RIGHT * 4.5 + DOWN * 0.32)

        arrows = VGroup(
            Arrow(full_ne.get_right(), left_ne.get_left(), buff=0.12, color=BLUE),
            Arrow(full_ne.get_right(), right_ne.get_left(), buff=0.12, color=GREEN),
        )

        self.play(FadeIn(title), Write(design))
        self.play(FadeIn(matrix_group, shift=UP), FadeIn(bracket_label))
        self.play(FadeIn(full_ne, scale=0.96))
        self.play(Create(arrows), FadeIn(split, shift=LEFT))
        self.wait(1.0)
        self.play(FadeOut(VGroup(title, design, matrix_group, bracket_label, full_ne, split, arrows)))

    def partial_out_x1(self) -> None:
        title = self.title(
            "Step 2: turn X1 into an annihilator",
            "The auxiliary problem uses the residual maker for the first regressor block.",
        )
        m1_def = self.card(
            "annihilatorMatrix X1",
            self.formula(r"M_1=I-X_1(X_1^TX_1)^{-1}X_1^T", font_size=29),
            PURPLE,
            width=6.2,
        )
        m1_zero = self.card(
            "annihilator_mul_X",
            self.formula(r"M_1X_1=0", font_size=38),
            RED,
            width=3.7,
        )
        m1_ortho = self.card(
            "regressors_transpose_mul_annihilator",
            self.formula(r"X_1^TM_1=0", font_size=34),
            BLUE,
            width=5.0,
        )
        residualized = self.card(
            "residualizedRegressors",
            self.formula(r"\widetilde X_2=M_1X_2,\qquad \widetilde y=M_1y", font_size=31),
            GREEN,
            width=5.7,
        )

        m1_def.next_to(title, DOWN, buff=0.45).shift(LEFT * 3.6)
        m1_zero.next_to(m1_def, DOWN, buff=0.42)
        m1_ortho.next_to(title, DOWN, buff=0.45).shift(RIGHT * 3.55)
        residualized.next_to(m1_ortho, DOWN, buff=0.42)

        plane = NumberPlane(
            x_range=(-3, 3, 1),
            y_range=(-2, 2, 1),
            x_length=5.2,
            y_length=3.3,
            background_line_style={"stroke_color": GRID, "stroke_width": 1, "stroke_opacity": 0.6},
            axis_config={"stroke_color": GRID, "stroke_width": 1},
        )
        plane.to_edge(DOWN, buff=0.28)

        x1_axis = Line(plane.c2p(-2.5, -0.8), plane.c2p(2.5, 0.8), color=BLUE, stroke_width=6)
        x2_vec = Arrow(plane.c2p(0, 0), plane.c2p(1.7, 1.35), buff=0, color=GREEN, stroke_width=6)
        x2_proj = Arrow(plane.c2p(0, 0), plane.c2p(1.05, 0.34), buff=0, color=BLUE, stroke_width=5)
        x2_resid = Arrow(plane.c2p(1.05, 0.34), plane.c2p(1.7, 1.35), buff=0, color=GREEN, stroke_width=5)
        x1_lab = Text("span(X1)", font_size=18, color=BLUE).next_to(x1_axis, DOWN, buff=0.08)
        x2_lab = Text("X2", font_size=18, color=GREEN).next_to(x2_vec.get_end(), RIGHT, buff=0.08)
        resid_lab = Text("M1 X2", font_size=18, color=GREEN).next_to(x2_resid, RIGHT, buff=0.08)

        self.play(FadeIn(title), FadeIn(m1_def, shift=DOWN))
        self.play(FadeIn(m1_zero, shift=DOWN), FadeIn(m1_ortho, shift=DOWN))
        self.play(Create(plane), Create(x1_axis), FadeIn(x1_lab))
        self.play(GrowArrow(x2_vec), FadeIn(x2_lab))
        self.play(TransformFromCopy(x2_vec, x2_proj), GrowArrow(x2_resid), FadeIn(resid_lab))
        self.play(FadeIn(residualized, shift=UP))
        self.wait(1.0)
        self.play(
            FadeOut(
                VGroup(
                    title,
                    m1_def,
                    m1_zero,
                    m1_ortho,
                    residualized,
                    plane,
                    x1_axis,
                    x2_vec,
                    x2_proj,
                    x2_resid,
                    x1_lab,
                    x2_lab,
                    resid_lab,
                )
            )
        )

    def auxiliary_regression(self) -> None:
        title = self.title(
            "Step 3: test the full beta2 inside the residualized regression",
            "The key bridge rewrites the auxiliary residual as the full residual after applying M1.",
        )
        aux_resid = self.card(
            "fwl_auxiliary_residual_eq_annihilator_full_residual",
            self.formula(
                r"M_1y-(M_1X_2)\hat\beta_2^{full}"
                r"=M_1\hat e_{full}",
                font_size=30,
            ),
            GOLD,
            width=7.35,
        )
        aux_resid.next_to(title, DOWN, buff=0.45)

        steps = VGroup(
            self.card(
                "split fitted values",
                self.formula(r"X\hat\beta=X_1\hat\beta_1+X_2\hat\beta_2", font_size=28),
                BLUE,
                width=4.8,
            ),
            self.card(
                "annihilate X1 part",
                self.formula(r"M_1X_1\hat\beta_1=0", font_size=30),
                RED,
                width=4.35,
            ),
            self.card(
                "keep residualized X2",
                self.formula(r"M_1X_2\hat\beta_2=\widetilde X_2\hat\beta_2", font_size=28),
                GREEN,
                width=4.85,
            ),
        ).arrange(RIGHT, buff=0.3)
        steps.next_to(aux_resid, DOWN, buff=0.55)

        normal = self.card(
            "fwl_fromColsRightBeta_normal_equations",
            self.formula(
                r"\widetilde X_2^T"
                r"\left(M_1y-\widetilde X_2\hat\beta_2^{full}\right)=0",
                font_size=29,
            ),
            GREEN,
            width=8.0,
        )
        normal.to_edge(DOWN, buff=0.55)

        arrows = VGroup(
            Arrow(steps[0].get_top(), aux_resid.get_bottom(), buff=0.1, color=BLUE),
            Arrow(steps[1].get_top(), aux_resid.get_bottom(), buff=0.1, color=RED),
            Arrow(steps[2].get_top(), aux_resid.get_bottom(), buff=0.1, color=GREEN),
            Arrow(aux_resid.get_bottom(), normal.get_top(), buff=0.15, color=GOLD),
        )

        self.play(FadeIn(title), FadeIn(aux_resid, scale=0.97))
        self.play(LaggedStart(*[FadeIn(step, shift=UP) for step in steps], lag_ratio=0.18))
        self.play(Create(arrows[:3]))
        self.play(Create(arrows[3]), FadeIn(normal, shift=UP))
        self.wait(1.0)
        self.play(FadeOut(VGroup(title, aux_resid, steps, normal, arrows)))

    def coefficient_identity(self) -> None:
        title = self.title(
            "Step 4: uniqueness turns normal equations into coefficient equality",
            "Once beta2 from the full regression satisfies the auxiliary normal equations, OLS uniqueness closes the theorem.",
        )
        left = self.card(
            "candidate",
            self.formula(r"\hat\beta_2^{full}", font_size=42),
            BLUE,
            width=3.7,
        )
        middle = self.card(
            "satisfies",
            self.formula(r"\widetilde X_2^T(\widetilde y-\widetilde X_2b)=0", font_size=29),
            GOLD,
            width=5.6,
        )
        right = self.card(
            "unique OLS solution",
            self.formula(r"\hat\beta_{FWL}", font_size=42),
            GREEN,
            width=3.7,
        )
        row = VGroup(left, middle, right).arrange(RIGHT, buff=0.32)
        row.next_to(title, DOWN, buff=0.6)

        bridge = Arrow(left.get_right(), middle.get_left(), buff=0.14, color=GOLD)
        unique = Arrow(middle.get_right(), right.get_left(), buff=0.14, color=GREEN)

        theorem = self.card(
            "fromColsRightBeta_eq_fwlBeta",
            self.formula(
                r"\operatorname{fromColsRightBeta}(X_1,X_2,y)"
                r"=\operatorname{fwlBeta}(X_1,X_2,y)",
                font_size=27,
            ),
            PURPLE,
            width=9.8,
        )
        theorem.to_edge(DOWN, buff=0.85)

        invert = self.label(
            "Invertibility assumptions make the two OLS problems uniquely solvable.",
            font_size=20,
            color=MUTED,
        )
        invert.next_to(row, DOWN, buff=0.42)

        self.play(FadeIn(title), FadeIn(row, shift=DOWN))
        self.play(Create(bridge), Create(unique))
        self.play(FadeIn(invert, shift=UP))
        self.play(FadeIn(theorem, scale=0.98))
        self.wait(1.0)
        self.play(FadeOut(VGroup(title, row, bridge, unique, invert, theorem)))

    def residual_and_sequential_maker(self) -> None:
        title = self.title(
            "Step 5: residual equality and the sequential residual maker",
            "The coefficient identity is reused to compare residuals, then the geometry is packaged as a matrix identity.",
        )
        residual_eq = self.card(
            "fwl_residual_eq_full_residual",
            self.formula(
                r"\operatorname{residual}(M_1X_2,M_1y)=\operatorname{residual}([X_1\;X_2],y)",
                font_size=27,
            ),
            GOLD,
            width=9.8,
        )
        residual_eq.next_to(title, DOWN, buff=0.5)

        facts = VGroup(
            self.card(
                "coefficient bridge",
                self.formula(r"\hat\beta_2^{full}=\hat\beta_{FWL}", font_size=29),
                PURPLE,
                width=4.35,
            ),
            self.card(
                "full residual fixed by M1",
                self.formula(r"X_1^T\hat e=0\Rightarrow M_1\hat e=\hat e", font_size=27),
                BLUE,
                width=5.15,
            ),
        ).arrange(RIGHT, buff=0.45)
        facts.next_to(residual_eq, DOWN, buff=0.55)

        maker = self.card(
            "fwl_residual_maker_mul_fromCols",
            self.formula(r"M_{M_1X_2}\,M_1\,[X_1\;X_2]=0", font_size=34),
            GREEN,
            width=6.8,
        )
        maker.to_edge(DOWN, buff=0.62)

        left_path = Arrow(facts[0].get_top(), residual_eq.get_bottom(), buff=0.14, color=PURPLE)
        right_path = Arrow(facts[1].get_top(), residual_eq.get_bottom(), buff=0.14, color=BLUE)
        down = Arrow(residual_eq.get_bottom(), maker.get_top(), buff=0.16, color=GREEN)

        self.play(FadeIn(title), FadeIn(residual_eq, scale=0.97))
        self.play(FadeIn(facts, shift=UP), Create(left_path), Create(right_path))
        self.play(Create(down), FadeIn(maker, shift=UP))
        self.wait(1.0)
        self.play(FadeOut(VGroup(title, residual_eq, facts, maker, left_path, right_path, down)))

    def dependency_map(self) -> None:
        title = self.title(
            "Lean dependency map",
            "The file builds theorem-shaped bridges from full OLS to the residualized problem.",
        )
        nodes = {
            "left": self.theorem_node("normal_equations_fromCols_left", "X1 block normal equation", BLUE),
            "right": self.theorem_node("normal_equations_fromCols_right", "X2 block normal equation", GREEN),
            "ann": self.theorem_node(
                "regressors_transpose_mul_annihilator",
                "transpose annihilator bridge",
                PURPLE,
            ),
            "residreg": self.theorem_node("residualizedRegressors", "definition: M1 X2", GREEN),
            "aux": self.theorem_node(
                "fwl_auxiliary_residual_eq_annihilator_full_residual",
                "auxiliary residual rewrite",
                GOLD,
                width=4.75,
            ),
            "auxne": self.theorem_node(
                "fwl_fromColsRightBeta_normal_equations",
                "full beta2 solves auxiliary NE",
                GREEN,
                width=4.75,
            ),
            "coef": self.theorem_node("fromColsRightBeta_eq_fwlBeta", "coefficient identity", PURPLE),
            "resid": self.theorem_node("fwl_residual_eq_full_residual", "residual identity", GOLD),
            "maker": self.theorem_node(
                "fwl_residual_maker_mul_fromCols",
                "sequential maker annihilates X",
                RED,
            ),
        }

        positions = {
            "left": LEFT * 5.35 + UP * 2.25,
            "right": LEFT * 5.35 + UP * 1.05,
            "ann": LEFT * 5.35 + DOWN * 0.15,
            "residreg": LEFT * 5.35 + DOWN * 1.35,
            "aux": LEFT * 0.55 + UP * 1.45,
            "auxne": LEFT * 0.55 + DOWN * 0.85,
            "coef": RIGHT * 4.65 + UP * 1.45,
            "resid": RIGHT * 4.65 + DOWN * 0.15,
            "maker": RIGHT * 4.65 + DOWN * 1.75,
        }
        for key, pos in positions.items():
            nodes[key].move_to(pos)

        node_group = VGroup(*nodes.values())
        node_group.next_to(title, DOWN, buff=0.45)

        edges = VGroup(
            Arrow(nodes["left"].get_right(), nodes["auxne"].get_left(), buff=0.16, color=BLUE),
            Arrow(nodes["right"].get_right(), nodes["auxne"].get_left(), buff=0.16, color=GREEN),
            Arrow(nodes["residreg"].get_right(), nodes["aux"].get_left(), buff=0.16, color=GREEN),
            Arrow(nodes["aux"].get_bottom(), nodes["auxne"].get_top(), buff=0.16, color=GOLD),
            Arrow(nodes["auxne"].get_right(), nodes["coef"].get_left(), buff=0.16, color=GREEN),
            Arrow(nodes["coef"].get_bottom(), nodes["resid"].get_top(), buff=0.16, color=PURPLE),
            Arrow(nodes["left"].get_right(), nodes["resid"].get_left(), buff=0.16, color=BLUE),
            Arrow(nodes["ann"].get_right(), nodes["residreg"].get_left(), buff=0.16, color=PURPLE),
            Arrow(nodes["ann"].get_right(), nodes["maker"].get_left(), buff=0.16, color=PURPLE),
            Arrow(nodes["residreg"].get_right(), nodes["maker"].get_left(), buff=0.16, color=GREEN),
        )
        edges.set_stroke(opacity=0.72, width=4)
        edges.set_z_index(0)
        node_group.set_z_index(2)
        title.set_z_index(3)

        self.play(FadeIn(title))
        self.play(LaggedStart(*[FadeIn(nodes[key], scale=0.96) for key in nodes], lag_ratio=0.08))
        self.play(LaggedStart(*[Create(edge) for edge in edges], lag_ratio=0.06))
        self.wait(1.4)
        self.play(FadeOut(VGroup(title, node_group, edges)))

    def outro(self) -> None:
        title = Text("FWL proof skeleton", font_size=40, weight=BOLD, color=TEXT)
        title.to_edge(UP, buff=0.75)
        bullets = VGroup(
            Text("1. Split full normal equations by column block.", font_size=25, color=TEXT),
            Text("2. Residualize y and X2 with M1.", font_size=25, color=TEXT),
            Text("3. Show full beta2 solves the residualized normal equations.", font_size=25, color=TEXT),
            Text("4. Invoke uniqueness to identify the coefficient.", font_size=25, color=TEXT),
            Text("5. Reuse the bridge for residual and maker identities.", font_size=25, color=TEXT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.26)
        bullets.next_to(title, DOWN, buff=0.65)

        closing = self.formula(
            r"\hat\beta_2^{full}=\hat\beta_{FWL}"
            r"\qquad\text{and}\qquad"
            r"\hat e_{full}=\hat e_{FWL}",
            font_size=36,
            color=GOLD,
        )
        closing.to_edge(DOWN, buff=0.9)

        self.play(FadeIn(title, shift=DOWN))
        self.play(LaggedStart(*[FadeIn(bullet, shift=RIGHT) for bullet in bullets], lag_ratio=0.12))
        self.play(Write(closing))
        self.wait(2.0)
