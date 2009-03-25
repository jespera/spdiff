static cairo_test_status_t
draw (cairo_t *cr, int width, int height)
{
    cairo_text_extents_t extents;
    cairo_font_options_t *font_options;
    static char black[] = "black", blue[] = "blue";

    /* We draw in the default black, so paint white first. */
    cairo_save (cr);
    cairo_set_source_rgb (cr, 1.0, 1.0, 1.0); /* white */
    cairo_paint (cr);
    cairo_restore (cr);

    cairo_select_font_face (cr, "Bitstream Vera Sans",
			    CAIRO_FONT_SLANT_NORMAL,
			    CAIRO_FONT_WEIGHT_NORMAL);
    cairo_set_font_size (cr, TEXT_SIZE);

    font_options = cairo_font_options_create ();
    cairo_get_font_options (cr, font_options);
    cairo_font_options_set_antialias (font_options, CAIRO_ANTIALIAS_GRAY);
    cairo_set_font_options (cr, font_options);

    cairo_font_options_destroy (font_options);

    cairo_set_source_rgb (cr, 0, 0, 0); /* black */
    cairo_text_extents (cr, black, &extents);
    cairo_move_to (cr, -extents.x_bearing, -extents.y_bearing);
    cairo_show_text (cr, black);
    cairo_translate (cr, 0, -extents.y_bearing + 1);

    cairo_set_source_rgb (cr, 0, 0, 1); /* blue */
    cairo_text_extents (cr, blue, &extents);
    cairo_move_to (cr, -extents.x_bearing, -extents.y_bearing);
    cairo_show_text (cr, blue);

    return CAIRO_TEST_SUCCESS;
}
