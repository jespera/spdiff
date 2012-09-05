static int __devinit timblogiw_probe(struct platform_device *pdev)
{
	int err;
	struct timblogiw *lw = NULL;
	struct timb_video_platform_data *pdata = pdev->dev.platform_data;

	if (!pdata) {
		dev_err(&pdev->dev, "No platform data\n");
		err = -EINVAL;
		goto err;
	}

	if (!pdata->encoder.module_name)
		dev_info(&pdev->dev, "Running without decoder\n");

	lw = devm_kzalloc(&pdev->dev, sizeof(*lw), GFP_KERNEL);
	if (!lw) {
		err = -ENOMEM;
		goto err;
	}

	if (pdev->dev.parent)
		lw->dev = pdev->dev.parent;
	else
		lw->dev = &pdev->dev;

	memcpy(&lw->pdata, pdata, sizeof(lw->pdata));

	mutex_init(&lw->lock);

	lw->video_dev = timblogiw_template;

	strlcpy(lw->v4l2_dev.name, DRIVER_NAME, sizeof(lw->v4l2_dev.name));
	err = v4l2_device_register(NULL, &lw->v4l2_dev);
	if (err)
		goto err;

	lw->video_dev.v4l2_dev = &lw->v4l2_dev;

	platform_set_drvdata(pdev, lw);
	video_set_drvdata(&lw->video_dev, lw);

	err = video_register_device(&lw->video_dev, VFL_TYPE_GRABBER, 0);
	if (err) {
		dev_err(&pdev->dev, "Error reg video: %d\n", err);
		goto err_request;
	}


	return 0;

err_request:
	platform_set_drvdata(pdev, NULL);
	v4l2_device_unregister(&lw->v4l2_dev);
err_register:
err:
	dev_err(&pdev->dev, "Failed to register: %d\n", err);

	return err;
}
